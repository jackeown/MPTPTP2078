%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6qSJD91IPs

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:21 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 667 expanded)
%              Number of leaves         :   30 ( 193 expanded)
%              Depth                    :   28
%              Number of atoms          : 1952 (13421 expanded)
%              Number of equality atoms :  157 ( 725 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k5_partfun1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k5_partfun1 @ X39 @ X40 @ X41 ) )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ ( k1_tarski @ X28 ) ) ) )
      | ( r1_partfun1 @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ ( k1_tarski @ X28 ) ) ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k5_partfun1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X33 = X30 )
      | ~ ( r1_partfun1 @ X33 @ X30 )
      | ~ ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v1_partfun1 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( sk_C @ X12 @ X11 )
       != X12 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ X34 @ ( k5_partfun1 @ X35 @ X36 @ X37 ) )
      | ~ ( r1_partfun1 @ X37 @ X34 )
      | ( X36 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X37 ) ) ),
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

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X18 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','86'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('88',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('89',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X17 ) @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('93',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('94',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('101',plain,(
    ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( X0
     != ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    $false ),
    inference(simplify,[status(thm)],['102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6qSJD91IPs
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 305 iterations in 0.170s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.64  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(l44_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (((X11) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 0.47/0.64          | ((X11) = (k1_tarski @ X12)))),
% 0.47/0.64      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.64  thf(t164_funct_2, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @
% 0.47/0.64           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.64             ( m1_subset_1 @
% 0.47/0.64               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.64        ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64            ( m1_subset_1 @
% 0.47/0.64              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64          ( ![D:$i]:
% 0.47/0.64            ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.64                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.64                ( m1_subset_1 @
% 0.47/0.64                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t158_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.47/0.64           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X38 @ (k5_partfun1 @ X39 @ X40 @ X41))
% 0.47/0.64          | (v1_funct_1 @ X38)
% 0.47/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.47/0.64          | ~ (v1_funct_1 @ X41))),
% 0.47/0.64      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.64          | (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf('4', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v1_funct_1 @ X0)
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (v1_funct_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (v1_funct_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (((X11) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 0.47/0.64          | ((X11) = (k1_tarski @ X12)))),
% 0.47/0.64      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X38 @ (k5_partfun1 @ X39 @ X40 @ X41))
% 0.47/0.64          | (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.47/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.47/0.64          | ~ (v1_funct_1 @ X41))),
% 0.47/0.64      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.64          | (m1_subset_1 @ X0 @ 
% 0.47/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X0 @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (m1_subset_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t143_partfun1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @
% 0.47/0.64           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.64             ( m1_subset_1 @
% 0.47/0.64               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.64           ( r1_partfun1 @ C @ D ) ) ) ))).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X26)
% 0.47/0.64          | ~ (m1_subset_1 @ X26 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ (k1_tarski @ X28))))
% 0.47/0.64          | (r1_partfun1 @ X29 @ X26)
% 0.47/0.64          | ~ (m1_subset_1 @ X29 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ (k1_tarski @ X28))))
% 0.47/0.64          | ~ (v1_funct_1 @ X29))),
% 0.47/0.64      inference('cnf', [status(esa)], [t143_partfun1])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.64  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | (r1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_D)
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | (r1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_D)
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['7', '20'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_partfun1 @ 
% 0.47/0.64           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64           sk_D)
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (v1_funct_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (((X11) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 0.47/0.64          | ((X11) = (k1_tarski @ X12)))),
% 0.47/0.64      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X38 @ (k5_partfun1 @ X39 @ X40 @ X41))
% 0.47/0.64          | (v1_funct_2 @ X38 @ X39 @ X40)
% 0.47/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.47/0.64          | ~ (v1_funct_1 @ X41))),
% 0.47/0.64      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.64          | (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.64  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ 
% 0.47/0.64               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (v1_funct_2 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['24', '29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (m1_subset_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.64  thf(t132_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.64           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.64         (((X23) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_funct_1 @ X24)
% 0.47/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.64          | (v1_partfun1 @ X24 @ X25)
% 0.47/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.64          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.47/0.64          | ~ (v1_funct_1 @ X24))),
% 0.47/0.64      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.64         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.47/0.64          | (v1_partfun1 @ X24 @ X25)
% 0.47/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.64          | ~ (v1_funct_1 @ X24)
% 0.47/0.64          | ((X23) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | (v1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (v1_funct_2 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64               sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['31', '33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | (v1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '34'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | (v1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | (v1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['23', '36'])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | (v1_partfun1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | (m1_subset_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.64         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.47/0.64          | (v1_partfun1 @ X24 @ X25)
% 0.47/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.64          | ~ (v1_funct_1 @ X24)
% 0.47/0.64          | ((X23) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.64        | (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t148_partfun1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.47/0.64               ( r1_partfun1 @ C @ D ) ) =>
% 0.47/0.64             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X30)
% 0.47/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.47/0.64          | ((X33) = (X30))
% 0.47/0.64          | ~ (r1_partfun1 @ X33 @ X30)
% 0.47/0.64          | ~ (v1_partfun1 @ X30 @ X31)
% 0.47/0.64          | ~ (v1_partfun1 @ X33 @ X31)
% 0.47/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.47/0.64          | ~ (v1_funct_1 @ X33))),
% 0.47/0.64      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.64          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.64          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | ((X0) = (sk_D))
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.64  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.64          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.64          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | ((X0) = (sk_D)))),
% 0.47/0.64      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (sk_D))
% 0.47/0.64          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ~ (v1_funct_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['45', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | ~ (v1_partfun1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64               sk_A)
% 0.47/0.64          | ~ (r1_partfun1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64               sk_D)
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['39', '51'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D))
% 0.47/0.64          | ~ (r1_partfun1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64               sk_D)
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['38', '52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | ~ (r1_partfun1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.64               sk_D)
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D))
% 0.47/0.64          | ~ (v1_funct_1 @ 
% 0.47/0.64               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['22', '54'])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ 
% 0.47/0.64             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64              = (sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['6', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64            = (sk_D))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (((X11) = (k1_xboole_0))
% 0.47/0.64          | ((sk_C @ X12 @ X11) != (X12))
% 0.47/0.64          | ((X11) = (k1_tarski @ X12)))),
% 0.47/0.64      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_D) != (X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64              = (k1_tarski @ X0))
% 0.47/0.64          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ sk_D))
% 0.47/0.64        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64         != (k1_tarski @ sk_D))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t155_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64           ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.64             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.64               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X34)
% 0.47/0.64          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.47/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.47/0.64          | (r2_hidden @ X34 @ (k5_partfun1 @ X35 @ X36 @ X37))
% 0.47/0.64          | ~ (r1_partfun1 @ X37 @ X34)
% 0.47/0.64          | ((X36) = (k1_xboole_0))
% 0.47/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.47/0.64          | ~ (v1_funct_1 @ X37))),
% 0.47/0.64      inference('cnf', [status(esa)], [t155_funct_2])).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0))
% 0.47/0.64          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.64  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.64          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['64', '70'])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.64          | (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf('74', plain, (((r1_partfun1 @ sk_C_1 @ sk_D) | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.64  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('76', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.47/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.64  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['71', '76', '77'])).
% 0.47/0.64  thf(t63_subset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.47/0.64       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      (![X18 : $i, X19 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (k1_tarski @ X18) @ (k1_zfmisc_1 @ X19))
% 0.47/0.64          | ~ (r2_hidden @ X18 @ X19))),
% 0.47/0.64      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.47/0.64  thf('80', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.64  thf(t3_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i]:
% 0.47/0.64         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.64  thf('82', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | (r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.47/0.64           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.64  thf(d10_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      (![X0 : $i, X2 : $i]:
% 0.47/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('84', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 0.47/0.64             (k1_tarski @ sk_D))
% 0.47/0.64        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64            = (k1_tarski @ sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.64  thf('85', plain,
% 0.47/0.64      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64         != (k1_tarski @ sk_D))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('86', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 0.47/0.64             (k1_tarski @ sk_D)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.47/0.64  thf('87', plain,
% 0.47/0.64      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_D))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['63', '86'])).
% 0.47/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.64  thf('88', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['87', '88'])).
% 0.47/0.64  thf('90', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.64  thf(t130_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.47/0.64       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf('91', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i]:
% 0.47/0.64         (((X16) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ (k1_tarski @ X17) @ X16) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.47/0.64  thf('92', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.47/0.64          | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['90', '91'])).
% 0.47/0.64  thf(t113_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf('93', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.47/0.64          | ((X14) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.64  thf('94', plain,
% 0.47/0.64      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['93'])).
% 0.47/0.64  thf('95', plain,
% 0.47/0.64      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['92', '94'])).
% 0.47/0.64  thf('96', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['95'])).
% 0.47/0.64  thf('97', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['95'])).
% 0.47/0.64  thf('98', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['96', '97'])).
% 0.47/0.64  thf('99', plain,
% 0.47/0.64      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.64         != (k1_tarski @ sk_D))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('100', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      (((k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) != (k1_tarski @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.64  thf('102', plain, (![X0 : $i]: ((X0) != (k1_tarski @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['98', '101'])).
% 0.47/0.64  thf('103', plain, ($false), inference('simplify', [status(thm)], ['102'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
