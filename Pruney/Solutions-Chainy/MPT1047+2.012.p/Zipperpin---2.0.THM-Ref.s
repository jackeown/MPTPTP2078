%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9YhzScU1CH

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:22 EST 2020

% Result     : Theorem 18.22s
% Output     : Refutation 18.26s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 462 expanded)
%              Number of leaves         :   31 ( 138 expanded)
%              Depth                    :   26
%              Number of atoms          : 2005 (8997 expanded)
%              Number of equality atoms :  158 ( 506 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X6
        = ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(t164_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
            = ( k1_tarski @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
              = ( k1_tarski @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X6
        = ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X27 ) ) ) )
      | ( r1_partfun1 @ X28 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X6
        = ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X24 @ X22 )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X24 @ X22 )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('47',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X32 = X29 )
      | ~ ( r1_partfun1 @ X32 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_partfun1 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ~ ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A )
      | ~ ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ~ ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ~ ( r1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['6','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( sk_C @ X7 @ X6 )
       != X7 )
      | ( X6
        = ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_D != X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_hidden @ X33 @ ( k5_partfun1 @ X34 @ X35 @ X36 ) )
      | ~ ( r1_partfun1 @ X36 @ X33 )
      | ( X35 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('74',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','76','77'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X15 ) ) )
      | ( X13 != X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','81'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['90'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
      | ( X20 != X21 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('94',plain,(
    ! [X21: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('98',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['90'])).

thf('99',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('100',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t131_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf('102',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 = X16 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X17 ) @ X18 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t131_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( X2 = X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['96','97','98','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9YhzScU1CH
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.22/18.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.22/18.43  % Solved by: fo/fo7.sh
% 18.22/18.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.22/18.43  % done 1281 iterations in 17.954s
% 18.22/18.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.22/18.43  % SZS output start Refutation
% 18.22/18.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.22/18.43  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 18.22/18.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.22/18.43  thf(sk_D_type, type, sk_D: $i).
% 18.22/18.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.22/18.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 18.22/18.43  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 18.22/18.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 18.22/18.43  thf(sk_A_type, type, sk_A: $i).
% 18.22/18.43  thf(sk_B_type, type, sk_B: $i).
% 18.22/18.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.22/18.43  thf(sk_C_1_type, type, sk_C_1: $i).
% 18.22/18.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.22/18.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.22/18.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.22/18.43  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 18.22/18.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 18.22/18.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 18.22/18.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.22/18.43  thf(l44_zfmisc_1, axiom,
% 18.22/18.43    (![A:$i,B:$i]:
% 18.22/18.43     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 18.22/18.43          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 18.22/18.43  thf('0', plain,
% 18.22/18.43      (![X6 : $i, X7 : $i]:
% 18.22/18.43         (((X6) = (k1_xboole_0))
% 18.22/18.43          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 18.22/18.43          | ((X6) = (k1_tarski @ X7)))),
% 18.22/18.43      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 18.22/18.43  thf(t164_funct_2, conjecture,
% 18.22/18.43    (![A:$i,B:$i,C:$i]:
% 18.22/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43         ( m1_subset_1 @
% 18.22/18.43           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43       ( ![D:$i]:
% 18.22/18.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 18.22/18.43             ( m1_subset_1 @
% 18.22/18.43               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 18.22/18.43  thf(zf_stmt_0, negated_conjecture,
% 18.22/18.43    (~( ![A:$i,B:$i,C:$i]:
% 18.22/18.43        ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43            ( m1_subset_1 @
% 18.22/18.43              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43          ( ![D:$i]:
% 18.22/18.43            ( ( ( v1_funct_1 @ D ) & 
% 18.22/18.43                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 18.22/18.43                ( m1_subset_1 @
% 18.22/18.43                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 18.22/18.43    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 18.22/18.43  thf('1', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_C_1 @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf(t158_funct_2, axiom,
% 18.22/18.43    (![A:$i,B:$i,C:$i]:
% 18.22/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.22/18.43       ( ![D:$i]:
% 18.22/18.43         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 18.22/18.43           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 18.22/18.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 18.22/18.43  thf('2', plain,
% 18.22/18.43      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 18.22/18.43         (~ (r2_hidden @ X37 @ (k5_partfun1 @ X38 @ X39 @ X40))
% 18.22/18.43          | (v1_funct_1 @ X37)
% 18.22/18.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 18.22/18.43          | ~ (v1_funct_1 @ X40))),
% 18.22/18.43      inference('cnf', [status(esa)], [t158_funct_2])).
% 18.22/18.43  thf('3', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ sk_C_1)
% 18.22/18.43          | (v1_funct_1 @ X0)
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['1', '2'])).
% 18.22/18.43  thf('4', plain, ((v1_funct_1 @ sk_C_1)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('5', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         ((v1_funct_1 @ X0)
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('demod', [status(thm)], ['3', '4'])).
% 18.22/18.43  thf('6', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (v1_funct_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['0', '5'])).
% 18.22/18.43  thf('7', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (v1_funct_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['0', '5'])).
% 18.22/18.43  thf('8', plain,
% 18.22/18.43      (![X6 : $i, X7 : $i]:
% 18.22/18.43         (((X6) = (k1_xboole_0))
% 18.22/18.43          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 18.22/18.43          | ((X6) = (k1_tarski @ X7)))),
% 18.22/18.43      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 18.22/18.43  thf('9', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_C_1 @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('10', plain,
% 18.22/18.43      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 18.22/18.43         (~ (r2_hidden @ X37 @ (k5_partfun1 @ X38 @ X39 @ X40))
% 18.22/18.43          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 18.22/18.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 18.22/18.43          | ~ (v1_funct_1 @ X40))),
% 18.22/18.43      inference('cnf', [status(esa)], [t158_funct_2])).
% 18.22/18.43  thf('11', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ sk_C_1)
% 18.22/18.43          | (m1_subset_1 @ X0 @ 
% 18.22/18.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['9', '10'])).
% 18.22/18.43  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('13', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         ((m1_subset_1 @ X0 @ 
% 18.22/18.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('demod', [status(thm)], ['11', '12'])).
% 18.22/18.43  thf('14', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (m1_subset_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['8', '13'])).
% 18.22/18.43  thf('15', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_D @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf(t143_partfun1, axiom,
% 18.22/18.43    (![A:$i,B:$i,C:$i]:
% 18.22/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43         ( m1_subset_1 @
% 18.22/18.43           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43       ( ![D:$i]:
% 18.22/18.43         ( ( ( v1_funct_1 @ D ) & 
% 18.22/18.43             ( m1_subset_1 @
% 18.22/18.43               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 18.22/18.43           ( r1_partfun1 @ C @ D ) ) ) ))).
% 18.22/18.43  thf('16', plain,
% 18.22/18.43      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X25)
% 18.22/18.43          | ~ (m1_subset_1 @ X25 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ (k1_tarski @ X27))))
% 18.22/18.43          | (r1_partfun1 @ X28 @ X25)
% 18.22/18.43          | ~ (m1_subset_1 @ X28 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ (k1_tarski @ X27))))
% 18.22/18.43          | ~ (v1_funct_1 @ X28))),
% 18.22/18.43      inference('cnf', [status(esa)], [t143_partfun1])).
% 18.22/18.43  thf('17', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X0)
% 18.22/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | (r1_partfun1 @ X0 @ sk_D)
% 18.22/18.43          | ~ (v1_funct_1 @ sk_D))),
% 18.22/18.43      inference('sup-', [status(thm)], ['15', '16'])).
% 18.22/18.43  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('19', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X0)
% 18.22/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | (r1_partfun1 @ X0 @ sk_D))),
% 18.22/18.43      inference('demod', [status(thm)], ['17', '18'])).
% 18.22/18.43  thf('20', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | (r1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_D)
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['14', '19'])).
% 18.22/18.43  thf('21', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | (r1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_D)
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['7', '20'])).
% 18.22/18.43  thf('22', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         ((r1_partfun1 @ 
% 18.22/18.43           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43           sk_D)
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['21'])).
% 18.22/18.43  thf('23', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (v1_funct_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['0', '5'])).
% 18.22/18.43  thf('24', plain,
% 18.22/18.43      (![X6 : $i, X7 : $i]:
% 18.22/18.43         (((X6) = (k1_xboole_0))
% 18.22/18.43          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 18.22/18.43          | ((X6) = (k1_tarski @ X7)))),
% 18.22/18.43      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 18.22/18.43  thf('25', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_C_1 @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('26', plain,
% 18.22/18.43      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 18.22/18.43         (~ (r2_hidden @ X37 @ (k5_partfun1 @ X38 @ X39 @ X40))
% 18.22/18.43          | (v1_funct_2 @ X37 @ X38 @ X39)
% 18.22/18.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 18.22/18.43          | ~ (v1_funct_1 @ X40))),
% 18.22/18.43      inference('cnf', [status(esa)], [t158_funct_2])).
% 18.22/18.43  thf('27', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ sk_C_1)
% 18.22/18.43          | (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['25', '26'])).
% 18.22/18.43  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('29', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         ((v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 18.22/18.43          | ~ (r2_hidden @ X0 @ 
% 18.22/18.43               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 18.22/18.43      inference('demod', [status(thm)], ['27', '28'])).
% 18.22/18.43  thf('30', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (v1_funct_2 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A @ (k1_tarski @ sk_B)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['24', '29'])).
% 18.22/18.43  thf('31', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (m1_subset_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['8', '13'])).
% 18.22/18.43  thf(t132_funct_2, axiom,
% 18.22/18.43    (![A:$i,B:$i,C:$i]:
% 18.22/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.22/18.43       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.22/18.43           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.22/18.43         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 18.22/18.43           ( v1_partfun1 @ C @ A ) ) ) ))).
% 18.22/18.43  thf('32', plain,
% 18.22/18.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 18.22/18.43         (((X22) = (k1_xboole_0))
% 18.22/18.43          | ~ (v1_funct_1 @ X23)
% 18.22/18.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 18.22/18.43          | (v1_partfun1 @ X23 @ X24)
% 18.22/18.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 18.22/18.43          | ~ (v1_funct_2 @ X23 @ X24 @ X22)
% 18.22/18.43          | ~ (v1_funct_1 @ X23))),
% 18.22/18.43      inference('cnf', [status(esa)], [t132_funct_2])).
% 18.22/18.43  thf('33', plain,
% 18.22/18.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 18.22/18.43         (~ (v1_funct_2 @ X23 @ X24 @ X22)
% 18.22/18.43          | (v1_partfun1 @ X23 @ X24)
% 18.22/18.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 18.22/18.43          | ~ (v1_funct_1 @ X23)
% 18.22/18.43          | ((X22) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['32'])).
% 18.22/18.43  thf('34', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | (v1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A)
% 18.22/18.43          | ~ (v1_funct_2 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43               sk_A @ (k1_tarski @ sk_B)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['31', '33'])).
% 18.22/18.43  thf('35', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | (v1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A)
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['30', '34'])).
% 18.22/18.43  thf('36', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | (v1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A)
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['35'])).
% 18.22/18.43  thf('37', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | (v1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A)
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['23', '36'])).
% 18.22/18.43  thf('38', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | (v1_partfun1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             sk_A)
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['37'])).
% 18.22/18.43  thf('39', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43            = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | (m1_subset_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['8', '13'])).
% 18.22/18.43  thf('40', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_D @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('41', plain,
% 18.22/18.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 18.22/18.43         (~ (v1_funct_2 @ X23 @ X24 @ X22)
% 18.22/18.43          | (v1_partfun1 @ X23 @ X24)
% 18.22/18.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 18.22/18.43          | ~ (v1_funct_1 @ X23)
% 18.22/18.43          | ((X22) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['32'])).
% 18.22/18.43  thf('42', plain,
% 18.22/18.43      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43        | ~ (v1_funct_1 @ sk_D)
% 18.22/18.43        | (v1_partfun1 @ sk_D @ sk_A)
% 18.22/18.43        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['40', '41'])).
% 18.22/18.43  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('45', plain,
% 18.22/18.43      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 18.22/18.43      inference('demod', [status(thm)], ['42', '43', '44'])).
% 18.22/18.43  thf('46', plain,
% 18.22/18.43      ((m1_subset_1 @ sk_D @ 
% 18.22/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf(t148_partfun1, axiom,
% 18.22/18.43    (![A:$i,B:$i,C:$i]:
% 18.22/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.22/18.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.22/18.43       ( ![D:$i]:
% 18.22/18.43         ( ( ( v1_funct_1 @ D ) & 
% 18.22/18.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.22/18.43           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 18.22/18.43               ( r1_partfun1 @ C @ D ) ) =>
% 18.22/18.43             ( ( C ) = ( D ) ) ) ) ) ))).
% 18.22/18.43  thf('47', plain,
% 18.22/18.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X29)
% 18.22/18.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 18.22/18.43          | ((X32) = (X29))
% 18.22/18.43          | ~ (r1_partfun1 @ X32 @ X29)
% 18.22/18.43          | ~ (v1_partfun1 @ X29 @ X30)
% 18.22/18.43          | ~ (v1_partfun1 @ X32 @ X30)
% 18.22/18.43          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 18.22/18.43          | ~ (v1_funct_1 @ X32))),
% 18.22/18.43      inference('cnf', [status(esa)], [t148_partfun1])).
% 18.22/18.43  thf('48', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X0)
% 18.22/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | ~ (v1_partfun1 @ X0 @ sk_A)
% 18.22/18.43          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 18.22/18.43          | ~ (r1_partfun1 @ X0 @ sk_D)
% 18.22/18.43          | ((X0) = (sk_D))
% 18.22/18.43          | ~ (v1_funct_1 @ sk_D))),
% 18.22/18.43      inference('sup-', [status(thm)], ['46', '47'])).
% 18.22/18.43  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 18.22/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.22/18.43  thf('50', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ X0)
% 18.22/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | ~ (v1_partfun1 @ X0 @ sk_A)
% 18.22/18.43          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 18.22/18.43          | ~ (r1_partfun1 @ X0 @ sk_D)
% 18.22/18.43          | ((X0) = (sk_D)))),
% 18.22/18.43      inference('demod', [status(thm)], ['48', '49'])).
% 18.22/18.43  thf('51', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((X0) = (sk_D))
% 18.22/18.43          | ~ (r1_partfun1 @ X0 @ sk_D)
% 18.22/18.43          | ~ (v1_partfun1 @ X0 @ sk_A)
% 18.22/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.22/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.22/18.43          | ~ (v1_funct_1 @ X0))),
% 18.22/18.43      inference('sup-', [status(thm)], ['45', '50'])).
% 18.22/18.43  thf('52', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | ~ (v1_partfun1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43               sk_A)
% 18.22/18.43          | ~ (r1_partfun1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43               sk_D)
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['39', '51'])).
% 18.22/18.43  thf('53', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D))
% 18.22/18.43          | ~ (r1_partfun1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43               sk_D)
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['38', '52'])).
% 18.22/18.43  thf('54', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | ~ (r1_partfun1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 18.22/18.43               sk_D)
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['53'])).
% 18.22/18.43  thf('55', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D))
% 18.22/18.43          | ~ (v1_funct_1 @ 
% 18.22/18.43               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 18.22/18.43      inference('sup-', [status(thm)], ['22', '54'])).
% 18.22/18.43  thf('56', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (~ (v1_funct_1 @ 
% 18.22/18.43             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['55'])).
% 18.22/18.43  thf('57', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43              = (sk_D)))),
% 18.22/18.43      inference('sup-', [status(thm)], ['6', '56'])).
% 18.22/18.43  thf('58', plain,
% 18.22/18.43      (![X0 : $i]:
% 18.22/18.43         (((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.22/18.43            = (sk_D))
% 18.22/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.22/18.43              = (k1_tarski @ X0))
% 18.22/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.22/18.43      inference('simplify', [status(thm)], ['57'])).
% 18.26/18.43  thf('59', plain,
% 18.26/18.43      (![X6 : $i, X7 : $i]:
% 18.26/18.43         (((X6) = (k1_xboole_0))
% 18.26/18.43          | ((sk_C @ X7 @ X6) != (X7))
% 18.26/18.43          | ((X6) = (k1_tarski @ X7)))),
% 18.26/18.43      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 18.26/18.43  thf('60', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (((sk_D) != (X0))
% 18.26/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 18.26/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.26/18.43              = (k1_tarski @ X0))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.26/18.43              = (k1_tarski @ X0))
% 18.26/18.43          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.26/18.43      inference('sup-', [status(thm)], ['58', '59'])).
% 18.26/18.43  thf('61', plain,
% 18.26/18.43      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.26/18.43            = (k1_tarski @ sk_D))
% 18.26/18.43        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.26/18.43      inference('simplify', [status(thm)], ['60'])).
% 18.26/18.43  thf('62', plain,
% 18.26/18.43      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.26/18.43         != (k1_tarski @ sk_D))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('63', plain,
% 18.26/18.43      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 18.26/18.43      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 18.26/18.43  thf('64', plain,
% 18.26/18.43      ((m1_subset_1 @ sk_C_1 @ 
% 18.26/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('65', plain,
% 18.26/18.43      ((m1_subset_1 @ sk_D @ 
% 18.26/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf(t155_funct_2, axiom,
% 18.26/18.43    (![A:$i,B:$i,C:$i]:
% 18.26/18.43     ( ( ( v1_funct_1 @ C ) & 
% 18.26/18.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.26/18.43       ( ![D:$i]:
% 18.26/18.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 18.26/18.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.26/18.43           ( ( r1_partfun1 @ C @ D ) =>
% 18.26/18.43             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 18.26/18.43               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 18.26/18.43  thf('66', plain,
% 18.26/18.43      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 18.26/18.43         (~ (v1_funct_1 @ X33)
% 18.26/18.43          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 18.26/18.43          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 18.26/18.43          | (r2_hidden @ X33 @ (k5_partfun1 @ X34 @ X35 @ X36))
% 18.26/18.43          | ~ (r1_partfun1 @ X36 @ X33)
% 18.26/18.43          | ((X35) = (k1_xboole_0))
% 18.26/18.43          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 18.26/18.43          | ~ (v1_funct_1 @ X36))),
% 18.26/18.43      inference('cnf', [status(esa)], [t155_funct_2])).
% 18.26/18.43  thf('67', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (~ (v1_funct_1 @ X0)
% 18.26/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.26/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | ~ (r1_partfun1 @ X0 @ sk_D)
% 18.26/18.43          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0))
% 18.26/18.43          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 18.26/18.43          | ~ (v1_funct_1 @ sk_D))),
% 18.26/18.43      inference('sup-', [status(thm)], ['65', '66'])).
% 18.26/18.43  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('70', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (~ (v1_funct_1 @ X0)
% 18.26/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.26/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | ~ (r1_partfun1 @ X0 @ sk_D)
% 18.26/18.43          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0)))),
% 18.26/18.43      inference('demod', [status(thm)], ['67', '68', '69'])).
% 18.26/18.43  thf('71', plain,
% 18.26/18.43      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.26/18.43        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 18.26/18.43        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43        | ~ (v1_funct_1 @ sk_C_1))),
% 18.26/18.43      inference('sup-', [status(thm)], ['64', '70'])).
% 18.26/18.43  thf('72', plain,
% 18.26/18.43      ((m1_subset_1 @ sk_C_1 @ 
% 18.26/18.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('73', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (~ (v1_funct_1 @ X0)
% 18.26/18.43          | ~ (m1_subset_1 @ X0 @ 
% 18.26/18.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 18.26/18.43          | (r1_partfun1 @ X0 @ sk_D))),
% 18.26/18.43      inference('demod', [status(thm)], ['17', '18'])).
% 18.26/18.43  thf('74', plain, (((r1_partfun1 @ sk_C_1 @ sk_D) | ~ (v1_funct_1 @ sk_C_1))),
% 18.26/18.43      inference('sup-', [status(thm)], ['72', '73'])).
% 18.26/18.43  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('76', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 18.26/18.43      inference('demod', [status(thm)], ['74', '75'])).
% 18.26/18.43  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('78', plain,
% 18.26/18.43      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 18.26/18.43        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 18.26/18.43      inference('demod', [status(thm)], ['71', '76', '77'])).
% 18.26/18.43  thf(t129_zfmisc_1, axiom,
% 18.26/18.43    (![A:$i,B:$i,C:$i,D:$i]:
% 18.26/18.43     ( ( r2_hidden @
% 18.26/18.43         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 18.26/18.43       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 18.26/18.43  thf('79', plain,
% 18.26/18.43      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 18.26/18.43         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 18.26/18.43           (k2_zfmisc_1 @ X12 @ (k1_tarski @ X15)))
% 18.26/18.43          | ((X13) != (X15))
% 18.26/18.43          | ~ (r2_hidden @ X11 @ X12))),
% 18.26/18.43      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 18.26/18.43  thf('80', plain,
% 18.26/18.43      (![X11 : $i, X12 : $i, X15 : $i]:
% 18.26/18.43         (~ (r2_hidden @ X11 @ X12)
% 18.26/18.43          | (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 18.26/18.43             (k2_zfmisc_1 @ X12 @ (k1_tarski @ X15))))),
% 18.26/18.43      inference('simplify', [status(thm)], ['79'])).
% 18.26/18.43  thf('81', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ 
% 18.26/18.43             (k2_zfmisc_1 @ 
% 18.26/18.43              (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 18.26/18.43              (k1_tarski @ X0))))),
% 18.26/18.43      inference('sup-', [status(thm)], ['78', '80'])).
% 18.26/18.43  thf('82', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         ((r2_hidden @ (k4_tarski @ sk_D @ X0) @ 
% 18.26/18.43           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0)))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 18.26/18.43      inference('sup+', [status(thm)], ['63', '81'])).
% 18.26/18.43  thf(t113_zfmisc_1, axiom,
% 18.26/18.43    (![A:$i,B:$i]:
% 18.26/18.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 18.26/18.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 18.26/18.43  thf('83', plain,
% 18.26/18.43      (![X9 : $i, X10 : $i]:
% 18.26/18.43         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 18.26/18.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 18.26/18.43  thf('84', plain,
% 18.26/18.43      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 18.26/18.43      inference('simplify', [status(thm)], ['83'])).
% 18.26/18.43  thf('85', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         ((r2_hidden @ (k4_tarski @ sk_D @ X0) @ k1_xboole_0)
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 18.26/18.43      inference('demod', [status(thm)], ['82', '84'])).
% 18.26/18.43  thf('86', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.26/18.43          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ k1_xboole_0))),
% 18.26/18.43      inference('simplify', [status(thm)], ['85'])).
% 18.26/18.43  thf('87', plain,
% 18.26/18.43      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 18.26/18.43      inference('simplify', [status(thm)], ['83'])).
% 18.26/18.43  thf('88', plain,
% 18.26/18.43      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 18.26/18.43         (((X13) = (X14))
% 18.26/18.43          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 18.26/18.43               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 18.26/18.43      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 18.26/18.43  thf('89', plain,
% 18.26/18.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.26/18.43         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0) | ((X1) = (X0)))),
% 18.26/18.43      inference('sup-', [status(thm)], ['87', '88'])).
% 18.26/18.43  thf('90', plain,
% 18.26/18.43      (![X0 : $i, X1 : $i]:
% 18.26/18.43         (((k1_tarski @ sk_B) = (k1_xboole_0)) | ((X0) = (X1)))),
% 18.26/18.43      inference('sup-', [status(thm)], ['86', '89'])).
% 18.26/18.43  thf('91', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 18.26/18.43      inference('condensation', [status(thm)], ['90'])).
% 18.26/18.43  thf(t69_enumset1, axiom,
% 18.26/18.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 18.26/18.43  thf('92', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 18.26/18.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.26/18.43  thf(t16_zfmisc_1, axiom,
% 18.26/18.43    (![A:$i,B:$i]:
% 18.26/18.43     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 18.26/18.43          ( ( A ) = ( B ) ) ) ))).
% 18.26/18.43  thf('93', plain,
% 18.26/18.43      (![X20 : $i, X21 : $i]:
% 18.26/18.43         (~ (r1_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 18.26/18.43          | ((X20) != (X21)))),
% 18.26/18.43      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 18.26/18.43  thf('94', plain,
% 18.26/18.43      (![X21 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))),
% 18.26/18.43      inference('simplify', [status(thm)], ['93'])).
% 18.26/18.43  thf('95', plain,
% 18.26/18.43      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 18.26/18.43      inference('sup-', [status(thm)], ['92', '94'])).
% 18.26/18.43  thf('96', plain, (~ (r1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_B))),
% 18.26/18.43      inference('sup-', [status(thm)], ['91', '95'])).
% 18.26/18.43  thf('97', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 18.26/18.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.26/18.43  thf('98', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 18.26/18.43      inference('condensation', [status(thm)], ['90'])).
% 18.26/18.43  thf('99', plain,
% 18.26/18.43      (![X9 : $i, X10 : $i]:
% 18.26/18.43         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 18.26/18.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 18.26/18.43  thf('100', plain,
% 18.26/18.43      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 18.26/18.43      inference('simplify', [status(thm)], ['99'])).
% 18.26/18.43  thf('101', plain,
% 18.26/18.43      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 18.26/18.43      inference('simplify', [status(thm)], ['99'])).
% 18.26/18.43  thf(t131_zfmisc_1, axiom,
% 18.26/18.43    (![A:$i,B:$i,C:$i,D:$i]:
% 18.26/18.43     ( ( ( A ) != ( B ) ) =>
% 18.26/18.43       ( ( r1_xboole_0 @
% 18.26/18.43           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 18.26/18.43           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 18.26/18.43         ( r1_xboole_0 @
% 18.26/18.43           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 18.26/18.43           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 18.26/18.43  thf('102', plain,
% 18.26/18.43      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 18.26/18.43         (((X17) = (X16))
% 18.26/18.43          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X17) @ X18) @ 
% 18.26/18.43             (k2_zfmisc_1 @ (k1_tarski @ X16) @ X19)))),
% 18.26/18.43      inference('cnf', [status(esa)], [t131_zfmisc_1])).
% 18.26/18.43  thf('103', plain,
% 18.26/18.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.26/18.43         ((r1_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0))
% 18.26/18.43          | ((X2) = (X1)))),
% 18.26/18.43      inference('sup+', [status(thm)], ['101', '102'])).
% 18.26/18.43  thf('104', plain,
% 18.26/18.43      (![X0 : $i, X1 : $i]:
% 18.26/18.43         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) | ((X1) = (X0)))),
% 18.26/18.43      inference('sup+', [status(thm)], ['100', '103'])).
% 18.26/18.43  thf('105', plain,
% 18.26/18.43      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 18.26/18.43         != (k1_tarski @ sk_D))),
% 18.26/18.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.26/18.43  thf('106', plain,
% 18.26/18.43      (![X0 : $i]:
% 18.26/18.43         (((X0) != (k1_tarski @ sk_D))
% 18.26/18.43          | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 18.26/18.43      inference('sup-', [status(thm)], ['104', '105'])).
% 18.26/18.43  thf('107', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 18.26/18.43      inference('simplify', [status(thm)], ['106'])).
% 18.26/18.43  thf('108', plain, ($false),
% 18.26/18.43      inference('demod', [status(thm)], ['96', '97', '98', '107'])).
% 18.26/18.43  
% 18.26/18.43  % SZS output end Refutation
% 18.26/18.43  
% 18.26/18.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
