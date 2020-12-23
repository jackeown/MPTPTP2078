%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IAHfQX7oY5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 154 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  894 (2084 expanded)
%              Number of equality atoms :   73 ( 152 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t49_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                = k1_xboole_0 ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                  = k1_xboole_0 ) )
        <=> ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_funct_2])).

thf('0',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf(t143_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X19 @ X20 ) @ X20 )
      | ( r1_tarski @ X20 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k1_tarski @ ( sk_C_1 @ X19 @ X20 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X20 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
      | ( ( k2_relat_1 @ sk_C_2 )
        = sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ~ ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('49',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('52',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X17 ) )
      | ( ( k10_relat_1 @ X17 @ ( k1_tarski @ X18 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['28','29'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','46','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IAHfQX7oY5
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 134 iterations in 0.056s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(t49_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( ![D:$i]:
% 0.21/0.52           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.52                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.21/0.52                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.21/0.52         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ( ![D:$i]:
% 0.21/0.52              ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.52                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.21/0.52                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.21/0.52            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.21/0.52        | (r2_hidden @ sk_D @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.21/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X31 : $i]:
% 0.21/0.52         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 0.21/0.52          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52              != (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X31 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((![X31 : $i]:
% 0.21/0.52          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52             != (k1_xboole_0))
% 0.21/0.52           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.21/0.52       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf(d3_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X1 : $i, X3 : $i]:
% 0.21/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.21/0.52        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(l3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.52          | (r2_hidden @ X10 @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X1 : $i, X3 : $i]:
% 0.21/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.21/0.52        | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.21/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.52  thf(t143_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( ![C:$i]:
% 0.21/0.52           ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.52                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.21/0.52         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_1 @ X19 @ X20) @ X20)
% 0.21/0.52          | (r1_tarski @ X20 @ (k2_relat_1 @ X19))
% 0.21/0.52          | ~ (v1_relat_1 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X19 @ (k1_tarski @ (sk_C_1 @ X19 @ X20)))
% 0.21/0.52            = (k1_xboole_0))
% 0.21/0.52          | (r1_tarski @ X20 @ (k2_relat_1 @ X19))
% 0.21/0.52          | ~ (v1_relat_1 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.52          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.21/0.52           = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((![X31 : $i]:
% 0.21/0.52          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52             != (k1_xboole_0))
% 0.21/0.52           | ~ (r2_hidden @ X31 @ sk_B)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((k10_relat_1 @ sk_C_2 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.21/0.52           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52           | ~ (v1_relat_1 @ sk_C_2)
% 0.21/0.52           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52           | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.21/0.52          | (v1_relat_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf(fc6_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('30', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52           | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)
% 0.21/0.52           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_C_2)
% 0.21/0.52         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '32'])).
% 0.21/0.52  thf('34', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X4 : $i, X6 : $i]:
% 0.21/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.21/0.52         | ((k2_relat_1 @ sk_C_2) = (sk_B))))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.21/0.52         <= ((![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 0.21/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 0.21/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((((sk_B) != (sk_B)))
% 0.21/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.21/0.52             (![X31 : $i]:
% 0.21/0.52                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52                   != (k1_xboole_0))
% 0.21/0.52                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (~
% 0.21/0.52       (![X31 : $i]:
% 0.21/0.52          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.21/0.52             != (k1_xboole_0))
% 0.21/0.52           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.21/0.52       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.21/0.52        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52            = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52          = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.21/0.52           = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52          = (k1_xboole_0)))
% 0.21/0.52         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52                = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.21/0.52         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52                = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf(t142_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.52         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X18 @ (k2_relat_1 @ X17))
% 0.21/0.52          | ((k10_relat_1 @ X17 @ (k1_tarski @ X18)) != (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52           | ~ (v1_relat_1 @ sk_C_2)
% 0.21/0.52           | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52           | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_D @ sk_B)))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.21/0.52             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52                = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['50', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D @ sk_B))
% 0.21/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.21/0.52             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52                = (k1_xboole_0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.21/0.52          = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 0.21/0.52       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '59'])).
% 0.21/0.52  thf('61', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['1', '3', '44', '46', '60'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
