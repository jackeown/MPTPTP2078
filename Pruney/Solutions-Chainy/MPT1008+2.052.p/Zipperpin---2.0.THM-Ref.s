%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.29vCQeBqz9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:38 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 619 expanded)
%              Number of leaves         :   40 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          :  968 (7092 expanded)
%              Number of equality atoms :  121 ( 760 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X30: $i] :
      ( ( X30 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ ( k2_relset_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ ( k2_relset_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','10','11','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = o_0_0_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = o_0_0_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = o_0_0_xboole_0 ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','48'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != o_0_0_xboole_0 )
      | ( X13 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('56',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C_1 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    sk_C_1 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','57','61','62','65'])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_tarski @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C @ X2 @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ ( sk_C @ X2 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C @ X2 @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ ( sk_C @ X2 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_relat_1 @ ( sk_C @ X2 @ ( k1_tarski @ X1 ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ ( sk_C @ X2 @ ( k1_tarski @ X1 ) ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ ( sk_C @ X0 @ o_0_0_xboole_0 ) @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','57','61','62','65'])).

thf('76',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('77',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != o_0_0_xboole_0 )
      | ( X13 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( ( sk_C @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( ( sk_C @ X1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('83',plain,(
    ! [X1: $i] :
      ( ( sk_C @ X1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('84',plain,
    ( o_0_0_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','81','82','83'])).

thf('85',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('86',plain,(
    sk_C_1 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('87',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('88',plain,(
    sk_C_1 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('89',plain,(
    o_0_0_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.29vCQeBqz9
% 0.14/0.36  % Computer   : n020.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:18:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 330 iterations in 0.175s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.65  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.44/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.65  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(t29_mcart_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.65          ( ![B:$i]:
% 0.44/0.65            ( ~( ( r2_hidden @ B @ A ) & 
% 0.44/0.65                 ( ![C:$i,D:$i,E:$i]:
% 0.44/0.65                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.44/0.65                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      (![X30 : $i]:
% 0.44/0.65         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.44/0.65      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.44/0.65  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.44/0.65  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X30 : $i]:
% 0.44/0.65         (((X30) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf(t62_funct_2, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.65         ( m1_subset_1 @
% 0.44/0.65           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.65       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.65         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.65           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.65            ( m1_subset_1 @
% 0.44/0.65              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.65          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.65            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.65              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t6_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( r2_hidden @ C @ A ) =>
% 0.44/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X34 @ X35)
% 0.44/0.65          | ((X36) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_funct_1 @ X37)
% 0.44/0.65          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.44/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.44/0.65          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ 
% 0.44/0.65             (k2_relset_1 @ X35 @ X36 @ X37)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.44/0.65  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X34 @ X35)
% 0.44/0.65          | ((X36) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (v1_funct_1 @ X37)
% 0.44/0.65          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.44/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.44/0.65          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ 
% 0.44/0.65             (k2_relset_1 @ X35 @ X36 @ X37)))),
% 0.44/0.65      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.44/0.65           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1))
% 0.44/0.65          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_C_1)
% 0.44/0.65          | ((sk_B_1) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['3', '6'])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.65         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.44/0.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.44/0.65         = (k2_relat_1 @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.65  thf('11', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.44/0.65          | ((sk_B_1) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['7', '10', '11', '12'])).
% 0.44/0.65  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('16', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((((k1_tarski @ sk_A) = (o_0_0_xboole_0))
% 0.44/0.65        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.44/0.65           (k2_relat_1 @ sk_C_1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['2', '17'])).
% 0.44/0.65  thf(t7_ordinal1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      ((((k1_tarski @ sk_A) = (o_0_0_xboole_0))
% 0.44/0.65        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.44/0.65             (k1_funct_1 @ sk_C_1 @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X24 @ X25)
% 0.44/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('23', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.65  thf(d18_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ B ) =>
% 0.44/0.65       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (v4_relat_1 @ X11 @ X12)
% 0.44/0.65          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.44/0.65          | ~ (v1_relat_1 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ sk_C_1)
% 0.44/0.65        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( v1_relat_1 @ C ) ))).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X21)
% 0.44/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['25', '28'])).
% 0.44/0.65  thf(t69_enumset1, axiom,
% 0.44/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.65  thf('30', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.65  thf(l45_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.44/0.65       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.44/0.65            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         (((X9) = (k2_tarski @ X7 @ X8))
% 0.44/0.65          | ((X9) = (k1_tarski @ X8))
% 0.44/0.65          | ((X9) = (k1_tarski @ X7))
% 0.44/0.65          | ((X9) = (k1_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.44/0.65      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.44/0.65  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         (((X9) = (k2_tarski @ X7 @ X8))
% 0.44/0.65          | ((X9) = (k1_tarski @ X8))
% 0.44/0.65          | ((X9) = (k1_tarski @ X7))
% 0.44/0.65          | ((X9) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.44/0.65      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.44/0.65          | ((X1) = (o_0_0_xboole_0))
% 0.44/0.65          | ((X1) = (k1_tarski @ X0))
% 0.44/0.65          | ((X1) = (k1_tarski @ X0))
% 0.44/0.65          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((X1) = (k2_tarski @ X0 @ X0))
% 0.44/0.65          | ((X1) = (k1_tarski @ X0))
% 0.44/0.65          | ((X1) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      ((((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['29', '35'])).
% 0.44/0.65  thf('37', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      ((((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      ((((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.65  thf(t14_funct_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.65       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.44/0.65         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 0.44/0.65          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.44/0.65          | ~ (v1_funct_1 @ X18)
% 0.44/0.65          | ~ (v1_relat_1 @ X18))),
% 0.44/0.65      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.44/0.65          | ((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_C_1)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_C_1)
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('eq_res', [status(thm)], ['41'])).
% 0.44/0.65  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.44/0.65        | ((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.44/0.65         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.44/0.65         = (k2_relat_1 @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.65  thf('49', plain, (((k1_relat_1 @ sk_C_1) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['45', '48'])).
% 0.44/0.65  thf(t64_relat_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ A ) =>
% 0.44/0.65       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.65  thf('50', plain,
% 0.44/0.65      (![X13 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.44/0.65          | ((X13) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X13))),
% 0.44/0.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.44/0.65  thf('51', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('52', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (![X13 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X13) != (o_0_0_xboole_0))
% 0.44/0.65          | ((X13) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X13))),
% 0.44/0.65      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.44/0.65        | ~ (v1_relat_1 @ sk_C_1)
% 0.44/0.65        | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['49', '53'])).
% 0.44/0.65  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('56', plain,
% 0.44/0.65      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.65  thf('57', plain, (((sk_C_1) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.44/0.65  thf(t60_relat_1, axiom,
% 0.44/0.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.44/0.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.65  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.65  thf('59', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('60', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('61', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.65  thf('62', plain, (((sk_C_1) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.44/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.65  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.65  thf('64', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.65  thf('65', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 0.44/0.65      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.65  thf('66', plain, (((k1_tarski @ sk_A) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['20', '57', '61', '62', '65'])).
% 0.44/0.65  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ?[C:$i]:
% 0.44/0.65       ( ( ![D:$i]:
% 0.44/0.65           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.44/0.65         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.44/0.65         ( v1_relat_1 @ C ) ) ))).
% 0.44/0.65  thf('67', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C @ X14 @ X15)) = (X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.65  thf('68', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 0.44/0.65          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.44/0.65          | ~ (v1_funct_1 @ X18)
% 0.44/0.65          | ~ (v1_relat_1 @ X18))),
% 0.44/0.65      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.44/0.65  thf('69', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((X0) != (k1_tarski @ X1))
% 0.44/0.65          | ~ (v1_relat_1 @ (sk_C @ X2 @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ (sk_C @ X2 @ X0))
% 0.44/0.65          | ((k2_relat_1 @ (sk_C @ X2 @ X0))
% 0.44/0.65              = (k1_tarski @ (k1_funct_1 @ (sk_C @ X2 @ X0) @ X1))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf('70', plain, (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C @ X14 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.65  thf('71', plain, (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C @ X14 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((X0) != (k1_tarski @ X1))
% 0.44/0.65          | ((k2_relat_1 @ (sk_C @ X2 @ X0))
% 0.44/0.65              = (k1_tarski @ (k1_funct_1 @ (sk_C @ X2 @ X0) @ X1))))),
% 0.44/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.44/0.65  thf('73', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i]:
% 0.44/0.65         ((k2_relat_1 @ (sk_C @ X2 @ (k1_tarski @ X1)))
% 0.44/0.65           = (k1_tarski @ (k1_funct_1 @ (sk_C @ X2 @ (k1_tarski @ X1)) @ X1)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['72'])).
% 0.44/0.65  thf('74', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_relat_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))
% 0.44/0.65           = (k1_tarski @ (k1_funct_1 @ (sk_C @ X0 @ o_0_0_xboole_0) @ sk_A)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['66', '73'])).
% 0.44/0.65  thf('75', plain, (((k1_tarski @ sk_A) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['20', '57', '61', '62', '65'])).
% 0.44/0.65  thf('76', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C @ X14 @ X15)) = (X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.65  thf('77', plain,
% 0.44/0.65      (![X13 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X13) != (o_0_0_xboole_0))
% 0.44/0.65          | ((X13) = (o_0_0_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X13))),
% 0.44/0.65      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.44/0.65  thf('78', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((X0) != (o_0_0_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.44/0.65          | ((sk_C @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.65  thf('79', plain, (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C @ X14 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.65  thf('80', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((X0) != (o_0_0_xboole_0)) | ((sk_C @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.65  thf('81', plain,
% 0.44/0.65      (![X1 : $i]: ((sk_C @ X1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['80'])).
% 0.44/0.65  thf('82', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.65  thf('83', plain,
% 0.44/0.65      (![X1 : $i]: ((sk_C @ X1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['80'])).
% 0.44/0.65  thf('84', plain,
% 0.44/0.65      (((o_0_0_xboole_0) = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['74', '75', '81', '82', '83'])).
% 0.44/0.65  thf('85', plain,
% 0.44/0.65      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.65  thf('86', plain, (((sk_C_1) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.44/0.65  thf('87', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.65  thf('88', plain, (((sk_C_1) = (o_0_0_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.44/0.65  thf('89', plain,
% 0.44/0.65      (((o_0_0_xboole_0) != (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.44/0.65  thf('90', plain, ($false),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['84', '89'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
