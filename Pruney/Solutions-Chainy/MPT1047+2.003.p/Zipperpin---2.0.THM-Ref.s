%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gNcLmmwcPn

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:21 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 791 expanded)
%              Number of leaves         :   31 ( 227 expanded)
%              Depth                    :   28
%              Number of atoms          : 2007 (16019 expanded)
%              Number of equality atoms :  164 ( 818 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k5_partfun1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k5_partfun1 @ X41 @ X42 @ X43 ) )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X30 ) ) ) )
      | ( r1_partfun1 @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k5_partfun1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('33',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X35 = X32 )
      | ~ ( r1_partfun1 @ X35 @ X32 )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_partfun1 @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( sk_C @ X11 @ X10 )
       != X11 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( r2_hidden @ X36 @ ( k5_partfun1 @ X37 @ X38 @ X39 ) )
      | ~ ( r1_partfun1 @ X39 @ X36 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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

thf('79',plain,
    ( ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','76','77'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ sk_D @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('83',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','89'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('92',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['92'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('97',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['92'])).

thf('104',plain,(
    ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( X0
     != ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    $false ),
    inference(simplify,[status(thm)],['105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gNcLmmwcPn
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 325 iterations in 0.200s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.47/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.69  thf(l44_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.69          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i]:
% 0.47/0.69         (((X10) = (k1_xboole_0))
% 0.47/0.69          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.47/0.69          | ((X10) = (k1_tarski @ X11)))),
% 0.47/0.69      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.69  thf(t164_funct_2, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @
% 0.47/0.69           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.69             ( m1_subset_1 @
% 0.47/0.69               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.69        ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69            ( m1_subset_1 @
% 0.47/0.69              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69          ( ![D:$i]:
% 0.47/0.69            ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.69                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.69                ( m1_subset_1 @
% 0.47/0.69                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t158_funct_2, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.47/0.69           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X40 @ (k5_partfun1 @ X41 @ X42 @ X43))
% 0.47/0.69          | (v1_funct_1 @ X40)
% 0.47/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.47/0.69          | ~ (v1_funct_1 @ X43))),
% 0.47/0.69      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.69          | (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.69  thf('4', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v1_funct_1 @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (v1_funct_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.69  thf('7', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (v1_funct_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i]:
% 0.47/0.69         (((X10) = (k1_xboole_0))
% 0.47/0.69          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.47/0.69          | ((X10) = (k1_tarski @ X11)))),
% 0.47/0.69      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X40 @ (k5_partfun1 @ X41 @ X42 @ X43))
% 0.47/0.69          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.47/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.47/0.69          | ~ (v1_funct_1 @ X43))),
% 0.47/0.69      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.69          | (m1_subset_1 @ X0 @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.69  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('13', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X0 @ 
% 0.47/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (m1_subset_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t143_partfun1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @
% 0.47/0.69           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.69             ( m1_subset_1 @
% 0.47/0.69               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.69           ( r1_partfun1 @ C @ D ) ) ) ))).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X28)
% 0.47/0.69          | ~ (m1_subset_1 @ X28 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ (k1_tarski @ X30))))
% 0.47/0.69          | (r1_partfun1 @ X31 @ X28)
% 0.47/0.69          | ~ (m1_subset_1 @ X31 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ (k1_tarski @ X30))))
% 0.47/0.69          | ~ (v1_funct_1 @ X31))),
% 0.47/0.69      inference('cnf', [status(esa)], [t143_partfun1])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | (r1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_D)
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | (r1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_D)
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r1_partfun1 @ 
% 0.47/0.69           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69           sk_D)
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (v1_funct_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i]:
% 0.47/0.69         (((X10) = (k1_xboole_0))
% 0.47/0.69          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.47/0.69          | ((X10) = (k1_tarski @ X11)))),
% 0.47/0.69      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X40 @ (k5_partfun1 @ X41 @ X42 @ X43))
% 0.47/0.69          | (v1_funct_2 @ X40 @ X41 @ X42)
% 0.47/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.47/0.69          | ~ (v1_funct_1 @ X43))),
% 0.47/0.69      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ sk_C_1)
% 0.47/0.69          | (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.69  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (v1_funct_2 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['24', '29'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (m1_subset_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.69  thf(t132_funct_2, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.69           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.69           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.69         (((X25) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_funct_1 @ X26)
% 0.47/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.47/0.69          | (v1_partfun1 @ X26 @ X27)
% 0.47/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.47/0.69          | ~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.47/0.69          | ~ (v1_funct_1 @ X26))),
% 0.47/0.69      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.47/0.69  thf('33', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.69         (~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.47/0.69          | (v1_partfun1 @ X26 @ X27)
% 0.47/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.47/0.69          | ~ (v1_funct_1 @ X26)
% 0.47/0.69          | ((X25) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | (v1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A)
% 0.47/0.69          | ~ (v1_funct_2 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69               sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['31', '33'])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | (v1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A)
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '34'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | (v1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A)
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | (v1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A)
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['23', '36'])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | (v1_partfun1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             sk_A)
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | (m1_subset_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['8', '13'])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.69         (~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.47/0.69          | (v1_partfun1 @ X26 @ X27)
% 0.47/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.47/0.69          | ~ (v1_funct_1 @ X26)
% 0.47/0.69          | ((X25) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.69        | (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.69        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.69  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t148_partfun1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.47/0.69               ( r1_partfun1 @ C @ D ) ) =>
% 0.47/0.69             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X32)
% 0.47/0.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.47/0.69          | ((X35) = (X32))
% 0.47/0.69          | ~ (r1_partfun1 @ X35 @ X32)
% 0.47/0.69          | ~ (v1_partfun1 @ X32 @ X33)
% 0.47/0.69          | ~ (v1_partfun1 @ X35 @ X33)
% 0.47/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.47/0.69          | ~ (v1_funct_1 @ X35))),
% 0.47/0.69      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.69          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | ((X0) = (sk_D))
% 0.47/0.69          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.69  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.69          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | ((X0) = (sk_D)))),
% 0.47/0.69      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.69  thf('51', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((X0) = (sk_D))
% 0.47/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ~ (v1_funct_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['45', '50'])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | ~ (v1_partfun1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69               sk_A)
% 0.47/0.69          | ~ (r1_partfun1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69               sk_D)
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['39', '51'])).
% 0.47/0.69  thf('53', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D))
% 0.47/0.69          | ~ (r1_partfun1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69               sk_D)
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['38', '52'])).
% 0.47/0.69  thf('54', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | ~ (r1_partfun1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 0.47/0.69               sk_D)
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D))
% 0.47/0.69          | ~ (v1_funct_1 @ 
% 0.47/0.69               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '54'])).
% 0.47/0.69  thf('56', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ 
% 0.47/0.69             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69              = (sk_D)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '56'])).
% 0.47/0.69  thf('58', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69            = (sk_D))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.69  thf('59', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i]:
% 0.47/0.69         (((X10) = (k1_xboole_0))
% 0.47/0.69          | ((sk_C @ X11 @ X10) != (X11))
% 0.47/0.69          | ((X10) = (k1_tarski @ X11)))),
% 0.47/0.69      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((sk_D) != (X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69              = (k1_tarski @ X0))
% 0.47/0.69          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ sk_D))
% 0.47/0.69        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.69  thf('62', plain,
% 0.47/0.69      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69         != (k1_tarski @ sk_D))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.47/0.69  thf('64', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('65', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t155_funct_2, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69           ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.69             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.69               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.69  thf('66', plain,
% 0.47/0.69      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X36)
% 0.47/0.69          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.47/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.69          | (r2_hidden @ X36 @ (k5_partfun1 @ X37 @ X38 @ X39))
% 0.47/0.69          | ~ (r1_partfun1 @ X39 @ X36)
% 0.47/0.69          | ((X38) = (k1_xboole_0))
% 0.47/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.69          | ~ (v1_funct_1 @ X39))),
% 0.47/0.69      inference('cnf', [status(esa)], [t155_funct_2])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0))
% 0.47/0.69          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.47/0.69          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.69      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.69  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('70', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.69          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.47/0.69  thf('71', plain,
% 0.47/0.69      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['64', '70'])).
% 0.47/0.69  thf('72', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('73', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_funct_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.47/0.69          | (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf('74', plain, (((r1_partfun1 @ sk_C_1 @ sk_D) | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.69  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('76', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.47/0.69      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.69  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('78', plain,
% 0.47/0.69      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['71', '76', '77'])).
% 0.47/0.69  thf('79', plain,
% 0.47/0.69      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['71', '76', '77'])).
% 0.47/0.69  thf(t38_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.69       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.47/0.69  thf('80', plain,
% 0.47/0.69      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.47/0.69         ((r1_tarski @ (k2_tarski @ X21 @ X23) @ X24)
% 0.47/0.69          | ~ (r2_hidden @ X23 @ X24)
% 0.47/0.69          | ~ (r2_hidden @ X21 @ X24))),
% 0.47/0.69      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.69  thf('81', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ 
% 0.47/0.69               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69          | (r1_tarski @ (k2_tarski @ X0 @ sk_D) @ 
% 0.47/0.69             (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['79', '80'])).
% 0.47/0.69  thf('82', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | (r1_tarski @ (k2_tarski @ sk_D @ sk_D) @ 
% 0.47/0.69           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['78', '81'])).
% 0.47/0.69  thf(t69_enumset1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.69  thf('83', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf('84', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | (r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.47/0.69           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.69  thf('85', plain,
% 0.47/0.69      (((r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.47/0.69         (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.69  thf(d10_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.69  thf('86', plain,
% 0.47/0.69      (![X0 : $i, X2 : $i]:
% 0.47/0.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.69  thf('87', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 0.47/0.69             (k1_tarski @ sk_D))
% 0.47/0.69        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69            = (k1_tarski @ sk_D)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['85', '86'])).
% 0.47/0.69  thf('88', plain,
% 0.47/0.69      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69         != (k1_tarski @ sk_D))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('89', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 0.47/0.69             (k1_tarski @ sk_D)))),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.47/0.69  thf('90', plain,
% 0.47/0.69      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_D))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['63', '89'])).
% 0.47/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.69  thf('91', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.69  thf('92', plain,
% 0.47/0.69      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.47/0.69  thf('93', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['92'])).
% 0.47/0.69  thf(t130_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.47/0.69       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.69         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('94', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i]:
% 0.47/0.69         (((X15) = (k1_xboole_0))
% 0.47/0.69          | ((k2_zfmisc_1 @ (k1_tarski @ X16) @ X15) != (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.47/0.69  thf('95', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.47/0.69          | ((X0) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.69  thf(t113_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('96', plain,
% 0.47/0.69      (![X13 : $i, X14 : $i]:
% 0.47/0.69         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.47/0.69          | ((X13) != (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.69  thf('97', plain,
% 0.47/0.69      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['96'])).
% 0.47/0.69  thf('98', plain,
% 0.47/0.69      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['95', '97'])).
% 0.47/0.69  thf('99', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['98'])).
% 0.47/0.69  thf('100', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['98'])).
% 0.47/0.69  thf('101', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['99', '100'])).
% 0.47/0.69  thf('102', plain,
% 0.47/0.69      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 0.47/0.69         != (k1_tarski @ sk_D))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('103', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['92'])).
% 0.47/0.69  thf('104', plain,
% 0.47/0.69      (((k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) != (k1_tarski @ sk_D))),
% 0.47/0.69      inference('demod', [status(thm)], ['102', '103'])).
% 0.47/0.69  thf('105', plain, (![X0 : $i]: ((X0) != (k1_tarski @ sk_D))),
% 0.47/0.69      inference('sup-', [status(thm)], ['101', '104'])).
% 0.47/0.69  thf('106', plain, ($false), inference('simplify', [status(thm)], ['105'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
