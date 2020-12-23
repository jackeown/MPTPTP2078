%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sYgvQwUa0v

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:47 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  290 (6455 expanded)
%              Number of leaves         :   53 (1876 expanded)
%              Depth                    :   33
%              Number of atoms          : 2533 (162254 expanded)
%              Number of equality atoms :  171 (8150 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X42: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X37 @ X36 )
      | ( ( k1_relat_1 @ X37 )
        = X36 )
      | ~ ( v4_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','60'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('67',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X37 @ X36 )
      | ( ( k1_relat_1 @ X37 )
        = X36 )
      | ~ ( v4_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','73'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X38 )
       != X39 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['91','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','90','104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','73'])).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X38 )
       != X39 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','73'])).

thf('120',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X38 )
       != X39 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X38 ) @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','118','127'])).

thf('129',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X37 @ X36 )
      | ( ( k1_relat_1 @ X37 )
        = X36 )
      | ~ ( v4_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('132',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('135',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('136',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('139',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('141',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k10_relat_1 @ X19 @ X20 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X19 ) @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('146',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('147',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('149',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['139','149'])).

thf('151',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['62','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('153',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['156'])).

thf('158',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','73'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('169',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_tops_2 @ X44 @ X43 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('170',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('175',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174'])).

thf('176',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('178',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','176','177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','133','136'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','60'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        = ( k2_relat_1 @ sk_C ) )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('183',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('184',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('186',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['156'])).

thf('190',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','192'])).

thf('194',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['186','195'])).

thf('197',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('202',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('204',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203'])).

thf('205',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','204'])).

thf('206',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','205'])).

thf('207',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ sk_C )
         != ( k2_relat_1 @ sk_C ) )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','206'])).

thf('208',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_C @ X0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('209',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('210',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('212',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('214',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('219',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['212','217','218'])).

thf('220',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['156'])).

thf('221',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['219','220'])).

thf('222',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['178','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('224',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('225',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','225'])).

thf('227',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','226'])).

thf('228',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['61','228','229'])).

thf('231',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('232',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('234',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('235',plain,(
    $false ),
    inference(demod,[status(thm)],['10','232','233','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sYgvQwUa0v
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 921 iterations in 0.600s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.07  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.07  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.83/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.83/1.07  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.83/1.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.07  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.83/1.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.83/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.83/1.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.83/1.07  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.83/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.07  thf(t62_tops_2, conjecture,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_struct_0 @ A ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.07                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.07                 ( m1_subset_1 @
% 0.83/1.07                   C @ 
% 0.83/1.07                   ( k1_zfmisc_1 @
% 0.83/1.07                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.07               ( ( ( ( k2_relset_1 @
% 0.83/1.07                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.07                     ( k2_struct_0 @ B ) ) & 
% 0.83/1.07                   ( v2_funct_1 @ C ) ) =>
% 0.83/1.07                 ( ( ( k1_relset_1 @
% 0.83/1.07                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.07                       ( k2_tops_2 @
% 0.83/1.07                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.07                     ( k2_struct_0 @ B ) ) & 
% 0.83/1.07                   ( ( k2_relset_1 @
% 0.83/1.07                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.07                       ( k2_tops_2 @
% 0.83/1.07                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.07                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i]:
% 0.83/1.07        ( ( l1_struct_0 @ A ) =>
% 0.83/1.07          ( ![B:$i]:
% 0.83/1.07            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.07              ( ![C:$i]:
% 0.83/1.07                ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.07                    ( v1_funct_2 @
% 0.83/1.07                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.07                    ( m1_subset_1 @
% 0.83/1.07                      C @ 
% 0.83/1.07                      ( k1_zfmisc_1 @
% 0.83/1.07                        ( k2_zfmisc_1 @
% 0.83/1.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.07                  ( ( ( ( k2_relset_1 @
% 0.83/1.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.07                        ( k2_struct_0 @ B ) ) & 
% 0.83/1.07                      ( v2_funct_1 @ C ) ) =>
% 0.83/1.07                    ( ( ( k1_relset_1 @
% 0.83/1.07                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.07                          ( k2_tops_2 @
% 0.83/1.07                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.07                        ( k2_struct_0 @ B ) ) & 
% 0.83/1.07                      ( ( k2_relset_1 @
% 0.83/1.07                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.07                          ( k2_tops_2 @
% 0.83/1.07                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.07                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.83/1.07  thf('0', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.07  thf('1', plain,
% 0.83/1.07      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/1.07         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.83/1.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.07  thf('2', plain,
% 0.83/1.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.07         = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf(fc5_struct_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.07       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.83/1.07  thf('5', plain,
% 0.83/1.07      (![X42 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ (k2_struct_0 @ X42))
% 0.83/1.07          | ~ (l1_struct_0 @ X42)
% 0.83/1.07          | (v2_struct_0 @ X42))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | (v2_struct_0 @ sk_B)
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('8', plain,
% 0.83/1.07      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.83/1.07      inference('demod', [status(thm)], ['6', '7'])).
% 0.83/1.07  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('clc', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf(fc4_zfmisc_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.83/1.07  thf('11', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.83/1.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.07  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf(t8_boole, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.83/1.07  thf('13', plain,
% 0.83/1.07      (![X5 : $i, X6 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t8_boole])).
% 0.83/1.07  thf('14', plain,
% 0.83/1.07      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.07  thf('15', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '14'])).
% 0.83/1.07  thf(d3_struct_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.83/1.07  thf('16', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('17', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('18', plain,
% 0.83/1.07      (((m1_subset_1 @ sk_C @ 
% 0.83/1.07         (k1_zfmisc_1 @ 
% 0.83/1.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['16', '17'])).
% 0.83/1.07  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('20', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['18', '19'])).
% 0.83/1.07  thf(t3_subset, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.07  thf('21', plain,
% 0.83/1.07      (![X9 : $i, X10 : $i]:
% 0.83/1.07         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      ((r1_tarski @ sk_C @ 
% 0.83/1.07        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['20', '21'])).
% 0.83/1.07  thf(t10_xboole_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.83/1.07  thf('23', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.07         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.83/1.07  thf('24', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (r1_tarski @ sk_C @ 
% 0.83/1.07          (k2_xboole_0 @ X0 @ 
% 0.83/1.07           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.83/1.07  thf('25', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.83/1.07          | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['15', '24'])).
% 0.83/1.07  thf(t1_boole, axiom,
% 0.83/1.07    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.07  thf('26', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.83/1.07      inference('cnf', [status(esa)], [t1_boole])).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_tarski @ sk_C @ X0) | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['25', '26'])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('29', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('30', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('31', plain,
% 0.83/1.07      (((m1_subset_1 @ sk_C @ 
% 0.83/1.07         (k1_zfmisc_1 @ 
% 0.83/1.07          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['29', '30'])).
% 0.83/1.07  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('33', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['31', '32'])).
% 0.83/1.07  thf(cc5_funct_2, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.83/1.07       ( ![C:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.83/1.07             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.83/1.07          | (v1_partfun1 @ X33 @ X34)
% 0.83/1.07          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.83/1.07          | ~ (v1_funct_1 @ X33)
% 0.83/1.07          | (v1_xboole_0 @ X35))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.83/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.07        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.07        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['33', '34'])).
% 0.83/1.07  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('37', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('39', plain,
% 0.83/1.07      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['37', '38'])).
% 0.83/1.07  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('41', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('demod', [status(thm)], ['39', '40'])).
% 0.83/1.07  thf('42', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.83/1.07        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['35', '36', '41'])).
% 0.83/1.07  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('44', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['42', '43'])).
% 0.83/1.07  thf('45', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('clc', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf('46', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['44', '45'])).
% 0.83/1.07  thf('47', plain,
% 0.83/1.07      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['28', '46'])).
% 0.83/1.07  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('49', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['47', '48'])).
% 0.83/1.07  thf(d4_partfun1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.83/1.07       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.83/1.07  thf('50', plain,
% 0.83/1.07      (![X36 : $i, X37 : $i]:
% 0.83/1.07         (~ (v1_partfun1 @ X37 @ X36)
% 0.83/1.07          | ((k1_relat_1 @ X37) = (X36))
% 0.83/1.07          | ~ (v4_relat_1 @ X37 @ X36)
% 0.83/1.07          | ~ (v1_relat_1 @ X37))),
% 0.83/1.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.07  thf('51', plain,
% 0.83/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.83/1.07        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.83/1.07        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['49', '50'])).
% 0.83/1.07  thf('52', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(cc2_relat_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ A ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.83/1.07  thf('53', plain,
% 0.83/1.07      (![X12 : $i, X13 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.83/1.07          | (v1_relat_1 @ X12)
% 0.83/1.07          | ~ (v1_relat_1 @ X13))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.83/1.07  thf('54', plain,
% 0.83/1.07      ((~ (v1_relat_1 @ 
% 0.83/1.07           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.83/1.07        | (v1_relat_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['52', '53'])).
% 0.83/1.07  thf(fc6_relat_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.83/1.07  thf('55', plain,
% 0.83/1.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.83/1.07  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.07      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.07  thf('57', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['18', '19'])).
% 0.83/1.07  thf(cc2_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.83/1.07  thf('58', plain,
% 0.83/1.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.07         ((v4_relat_1 @ X24 @ X25)
% 0.83/1.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.07  thf('59', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['57', '58'])).
% 0.83/1.07  thf('60', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.83/1.07  thf('61', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_tarski @ sk_C @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['27', '60'])).
% 0.83/1.07  thf(t169_relat_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ A ) =>
% 0.83/1.07       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.83/1.07  thf('62', plain,
% 0.83/1.07      (![X18 : $i]:
% 0.83/1.07         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.83/1.07          | ~ (v1_relat_1 @ X18))),
% 0.83/1.07      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.83/1.07  thf('63', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['31', '32'])).
% 0.83/1.07  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('65', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.07      inference('demod', [status(thm)], ['63', '64'])).
% 0.83/1.07  thf('66', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['44', '45'])).
% 0.83/1.07  thf('67', plain,
% 0.83/1.07      (![X36 : $i, X37 : $i]:
% 0.83/1.07         (~ (v1_partfun1 @ X37 @ X36)
% 0.83/1.07          | ((k1_relat_1 @ X37) = (X36))
% 0.83/1.07          | ~ (v4_relat_1 @ X37 @ X36)
% 0.83/1.07          | ~ (v1_relat_1 @ X37))),
% 0.83/1.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.07  thf('68', plain,
% 0.83/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.83/1.07        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['66', '67'])).
% 0.83/1.07  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.07      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.07  thf('70', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('71', plain,
% 0.83/1.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.07         ((v4_relat_1 @ X24 @ X25)
% 0.83/1.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.07  thf('72', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['70', '71'])).
% 0.83/1.07  thf('73', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.83/1.07  thf('74', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.07      inference('demod', [status(thm)], ['65', '73'])).
% 0.83/1.07  thf(t31_funct_2, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.07       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.83/1.07         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.83/1.07           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.83/1.07           ( m1_subset_1 @
% 0.83/1.07             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.83/1.07  thf('75', plain,
% 0.83/1.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.83/1.07         (~ (v2_funct_1 @ X38)
% 0.83/1.07          | ((k2_relset_1 @ X40 @ X39 @ X38) != (X39))
% 0.83/1.07          | (m1_subset_1 @ (k2_funct_1 @ X38) @ 
% 0.83/1.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.83/1.07          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.83/1.07          | ~ (v1_funct_2 @ X38 @ X40 @ X39)
% 0.83/1.07          | ~ (v1_funct_1 @ X38))),
% 0.83/1.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.83/1.07  thf('76', plain,
% 0.83/1.07      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.07        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07           (k1_zfmisc_1 @ 
% 0.83/1.07            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.83/1.07        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07            != (k2_relat_1 @ sk_C))
% 0.83/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['74', '75'])).
% 0.83/1.07  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('78', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('79', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('80', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('81', plain,
% 0.83/1.07      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['79', '80'])).
% 0.83/1.07  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('83', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.07      inference('demod', [status(thm)], ['81', '82'])).
% 0.83/1.07  thf('84', plain,
% 0.83/1.07      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['78', '83'])).
% 0.83/1.07  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('86', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('demod', [status(thm)], ['84', '85'])).
% 0.83/1.07  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('88', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.83/1.07  thf('89', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.83/1.07  thf('90', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['88', '89'])).
% 0.83/1.07  thf('91', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('92', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('93', plain,
% 0.83/1.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.07         = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('94', plain,
% 0.83/1.07      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.07          = (k2_struct_0 @ sk_B))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['92', '93'])).
% 0.83/1.07  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('96', plain,
% 0.83/1.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.07         = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('demod', [status(thm)], ['94', '95'])).
% 0.83/1.07  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('99', plain,
% 0.83/1.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.83/1.07  thf('100', plain,
% 0.83/1.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07          = (k2_relat_1 @ sk_C))
% 0.83/1.07        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['91', '99'])).
% 0.83/1.07  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('102', plain,
% 0.83/1.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['100', '101'])).
% 0.83/1.07  thf('103', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.83/1.07  thf('104', plain,
% 0.83/1.07      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['102', '103'])).
% 0.83/1.07  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('106', plain,
% 0.83/1.07      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07         (k1_zfmisc_1 @ 
% 0.83/1.07          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.83/1.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['76', '77', '90', '104', '105'])).
% 0.83/1.07  thf('107', plain,
% 0.83/1.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.83/1.07  thf('108', plain,
% 0.83/1.07      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.83/1.07          | (v1_partfun1 @ X33 @ X34)
% 0.83/1.07          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.83/1.07          | ~ (v1_funct_1 @ X33)
% 0.83/1.07          | (v1_xboole_0 @ X35))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.83/1.07  thf('109', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.83/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.07        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.83/1.07             (k1_relat_1 @ sk_C))
% 0.83/1.07        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['107', '108'])).
% 0.83/1.07  thf('110', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.07      inference('demod', [status(thm)], ['65', '73'])).
% 0.83/1.07  thf('111', plain,
% 0.83/1.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.83/1.07         (~ (v2_funct_1 @ X38)
% 0.83/1.07          | ((k2_relset_1 @ X40 @ X39 @ X38) != (X39))
% 0.83/1.07          | (v1_funct_1 @ (k2_funct_1 @ X38))
% 0.83/1.07          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.83/1.07          | ~ (v1_funct_2 @ X38 @ X40 @ X39)
% 0.83/1.07          | ~ (v1_funct_1 @ X38))),
% 0.83/1.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.83/1.07  thf('112', plain,
% 0.83/1.07      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.07        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.07        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07            != (k2_relat_1 @ sk_C))
% 0.83/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['110', '111'])).
% 0.83/1.07  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('114', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['88', '89'])).
% 0.83/1.07  thf('115', plain,
% 0.83/1.07      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['102', '103'])).
% 0.83/1.07  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('117', plain,
% 0.83/1.07      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.83/1.07  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.07      inference('simplify', [status(thm)], ['117'])).
% 0.83/1.07  thf('119', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.07      inference('demod', [status(thm)], ['65', '73'])).
% 0.83/1.07  thf('120', plain,
% 0.83/1.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.83/1.07         (~ (v2_funct_1 @ X38)
% 0.83/1.07          | ((k2_relset_1 @ X40 @ X39 @ X38) != (X39))
% 0.83/1.07          | (v1_funct_2 @ (k2_funct_1 @ X38) @ X39 @ X40)
% 0.83/1.07          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.83/1.07          | ~ (v1_funct_2 @ X38 @ X40 @ X39)
% 0.83/1.07          | ~ (v1_funct_1 @ X38))),
% 0.83/1.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.83/1.07  thf('121', plain,
% 0.83/1.07      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.07        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.83/1.07           (k1_relat_1 @ sk_C))
% 0.83/1.07        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07            != (k2_relat_1 @ sk_C))
% 0.83/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['119', '120'])).
% 0.83/1.07  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('123', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['88', '89'])).
% 0.83/1.07  thf('124', plain,
% 0.83/1.07      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['102', '103'])).
% 0.83/1.07  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('126', plain,
% 0.83/1.07      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.83/1.07         (k1_relat_1 @ sk_C))
% 0.83/1.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.83/1.07  thf('127', plain,
% 0.83/1.07      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.83/1.07        (k1_relat_1 @ sk_C))),
% 0.83/1.07      inference('simplify', [status(thm)], ['126'])).
% 0.83/1.07  thf('128', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.83/1.07        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['109', '118', '127'])).
% 0.83/1.07  thf('129', plain,
% 0.83/1.07      (![X36 : $i, X37 : $i]:
% 0.83/1.07         (~ (v1_partfun1 @ X37 @ X36)
% 0.83/1.07          | ((k1_relat_1 @ X37) = (X36))
% 0.83/1.07          | ~ (v4_relat_1 @ X37 @ X36)
% 0.83/1.07          | ~ (v1_relat_1 @ X37))),
% 0.83/1.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.07  thf('130', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.83/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.07        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['128', '129'])).
% 0.83/1.07  thf('131', plain,
% 0.83/1.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.83/1.07  thf(cc1_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( v1_relat_1 @ C ) ))).
% 0.83/1.07  thf('132', plain,
% 0.83/1.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.07         ((v1_relat_1 @ X21)
% 0.83/1.07          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.07  thf('133', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['131', '132'])).
% 0.83/1.07  thf('134', plain,
% 0.83/1.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.83/1.07  thf('135', plain,
% 0.83/1.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.07         ((v4_relat_1 @ X24 @ X25)
% 0.83/1.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.07  thf('136', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['134', '135'])).
% 0.83/1.07  thf('137', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.83/1.07        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['130', '133', '136'])).
% 0.83/1.07  thf('138', plain,
% 0.83/1.07      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.07  thf('139', plain,
% 0.83/1.07      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.83/1.07        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['137', '138'])).
% 0.83/1.07  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(t155_funct_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.83/1.07       ( ( v2_funct_1 @ B ) =>
% 0.83/1.07         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.83/1.07  thf('141', plain,
% 0.83/1.07      (![X19 : $i, X20 : $i]:
% 0.83/1.07         (~ (v2_funct_1 @ X19)
% 0.83/1.07          | ((k10_relat_1 @ X19 @ X20)
% 0.83/1.07              = (k9_relat_1 @ (k2_funct_1 @ X19) @ X20))
% 0.83/1.07          | ~ (v1_funct_1 @ X19)
% 0.83/1.07          | ~ (v1_relat_1 @ X19))),
% 0.83/1.07      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.83/1.07  thf('142', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (v1_relat_1 @ sk_C)
% 0.83/1.07          | ((k10_relat_1 @ sk_C @ X0)
% 0.83/1.07              = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.83/1.07          | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['140', '141'])).
% 0.83/1.07  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.07      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.07  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('145', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.83/1.07  thf(t146_relat_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ A ) =>
% 0.83/1.07       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.83/1.07  thf('146', plain,
% 0.83/1.07      (![X17 : $i]:
% 0.83/1.07         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.83/1.07          | ~ (v1_relat_1 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.83/1.07  thf('147', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['145', '146'])).
% 0.83/1.07  thf('148', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['131', '132'])).
% 0.83/1.07  thf('149', plain,
% 0.83/1.07      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['147', '148'])).
% 0.83/1.07  thf('150', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 0.83/1.07          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['139', '149'])).
% 0.83/1.07  thf('151', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.07        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['62', '150'])).
% 0.83/1.07  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.07      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.07  thf('153', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.07        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['151', '152'])).
% 0.83/1.07  thf('154', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('155', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('156', plain,
% 0.83/1.07      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_B))
% 0.83/1.07        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07            != (k2_struct_0 @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('157', plain,
% 0.83/1.07      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_A)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('split', [status(esa)], ['156'])).
% 0.83/1.07  thf('158', plain,
% 0.83/1.07      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07           != (k2_struct_0 @ sk_A))
% 0.83/1.07         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['155', '157'])).
% 0.83/1.07  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('160', plain,
% 0.83/1.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_A)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('demod', [status(thm)], ['158', '159'])).
% 0.83/1.07  thf('161', plain,
% 0.83/1.07      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07           != (k2_struct_0 @ sk_A))
% 0.83/1.07         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['154', '160'])).
% 0.83/1.07  thf('162', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('163', plain,
% 0.83/1.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_A)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('demod', [status(thm)], ['161', '162'])).
% 0.83/1.07  thf('164', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('165', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.83/1.07  thf('166', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.83/1.07  thf('167', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('168', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_C @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.07      inference('demod', [status(thm)], ['65', '73'])).
% 0.83/1.07  thf(d4_tops_2, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.83/1.07         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.83/1.07  thf('169', plain,
% 0.83/1.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.83/1.07         (((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 0.83/1.07          | ~ (v2_funct_1 @ X45)
% 0.83/1.07          | ((k2_tops_2 @ X44 @ X43 @ X45) = (k2_funct_1 @ X45))
% 0.83/1.07          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.83/1.07          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.83/1.07          | ~ (v1_funct_1 @ X45))),
% 0.83/1.07      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.83/1.07  thf('170', plain,
% 0.83/1.07      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.07        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.83/1.07        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07            = (k2_funct_1 @ sk_C))
% 0.83/1.07        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.07        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07            != (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['168', '169'])).
% 0.83/1.07  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('172', plain,
% 0.83/1.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['88', '89'])).
% 0.83/1.07  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('174', plain,
% 0.83/1.07      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['102', '103'])).
% 0.83/1.07  thf('175', plain,
% 0.83/1.07      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07          = (k2_funct_1 @ sk_C))
% 0.83/1.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['170', '171', '172', '173', '174'])).
% 0.83/1.07  thf('176', plain,
% 0.83/1.07      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_funct_1 @ sk_C))),
% 0.83/1.07      inference('simplify', [status(thm)], ['175'])).
% 0.83/1.07  thf('177', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.83/1.07  thf('178', plain,
% 0.83/1.07      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_A))))),
% 0.83/1.07      inference('demod', [status(thm)],
% 0.83/1.07                ['163', '164', '165', '166', '167', '176', '177'])).
% 0.83/1.07  thf('179', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.83/1.07        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['130', '133', '136'])).
% 0.83/1.07  thf('180', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_tarski @ sk_C @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('demod', [status(thm)], ['27', '60'])).
% 0.83/1.07  thf('181', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.83/1.07          | (r1_tarski @ sk_C @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['179', '180'])).
% 0.83/1.07  thf('182', plain,
% 0.83/1.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.83/1.07  thf(redefinition_k1_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.83/1.07  thf('183', plain,
% 0.83/1.07      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.83/1.07         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.83/1.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.07  thf('184', plain,
% 0.83/1.07      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['182', '183'])).
% 0.83/1.07  thf('185', plain,
% 0.83/1.07      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.07         = (k2_funct_1 @ sk_C))),
% 0.83/1.07      inference('simplify', [status(thm)], ['175'])).
% 0.83/1.07  thf('186', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('187', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('188', plain,
% 0.83/1.07      (![X41 : $i]:
% 0.83/1.07         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.83/1.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.07  thf('189', plain,
% 0.83/1.07      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('split', [status(esa)], ['156'])).
% 0.83/1.07  thf('190', plain,
% 0.83/1.07      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07           != (k2_struct_0 @ sk_B))
% 0.83/1.07         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['188', '189'])).
% 0.83/1.07  thf('191', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('192', plain,
% 0.83/1.07      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['190', '191'])).
% 0.83/1.07  thf('193', plain,
% 0.83/1.07      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07           != (k2_struct_0 @ sk_B))
% 0.83/1.07         | ~ (l1_struct_0 @ sk_A)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['187', '192'])).
% 0.83/1.07  thf('194', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('195', plain,
% 0.83/1.07      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['193', '194'])).
% 0.83/1.07  thf('196', plain,
% 0.83/1.07      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07           != (k2_struct_0 @ sk_B))
% 0.83/1.07         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['186', '195'])).
% 0.83/1.07  thf('197', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('198', plain,
% 0.83/1.07      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          != (k2_struct_0 @ sk_B)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['196', '197'])).
% 0.83/1.07  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('200', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.83/1.07  thf('201', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.83/1.07  thf('202', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('203', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('204', plain,
% 0.83/1.07      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.83/1.07          != (k2_relat_1 @ sk_C)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)],
% 0.83/1.07                ['198', '199', '200', '201', '202', '203'])).
% 0.83/1.07  thf('205', plain,
% 0.83/1.07      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['185', '204'])).
% 0.83/1.07  thf('206', plain,
% 0.83/1.07      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['184', '205'])).
% 0.83/1.07  thf('207', plain,
% 0.83/1.07      ((![X0 : $i]:
% 0.83/1.07          (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.83/1.07           | (r1_tarski @ sk_C @ X0)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['181', '206'])).
% 0.83/1.07  thf('208', plain,
% 0.83/1.07      ((![X0 : $i]: (r1_tarski @ sk_C @ X0))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['207'])).
% 0.83/1.07  thf(t3_xboole_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.07  thf('209', plain,
% 0.83/1.07      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.83/1.07  thf('210', plain,
% 0.83/1.07      ((((sk_C) = (k1_xboole_0)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['208', '209'])).
% 0.83/1.07  thf('211', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.83/1.07      inference('clc', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf('212', plain,
% 0.83/1.07      ((~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.83/1.07         <= (~
% 0.83/1.07             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07                = (k2_struct_0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['210', '211'])).
% 0.83/1.07  thf('213', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf(fc11_relat_1, axiom,
% 0.83/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.83/1.07  thf('214', plain,
% 0.83/1.07      (![X14 : $i]:
% 0.83/1.07         ((v1_xboole_0 @ (k2_relat_1 @ X14)) | ~ (v1_xboole_0 @ X14))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.83/1.07  thf('215', plain,
% 0.83/1.07      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.07  thf('216', plain,
% 0.83/1.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_relat_1 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['214', '215'])).
% 0.83/1.07  thf('217', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['213', '216'])).
% 0.83/1.07  thf('218', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('219', plain,
% 0.83/1.07      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          = (k2_struct_0 @ sk_B)))),
% 0.83/1.07      inference('demod', [status(thm)], ['212', '217', '218'])).
% 0.83/1.07  thf('220', plain,
% 0.83/1.07      (~
% 0.83/1.07       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          = (k2_struct_0 @ sk_A))) | 
% 0.83/1.07       ~
% 0.83/1.07       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          = (k2_struct_0 @ sk_B)))),
% 0.83/1.07      inference('split', [status(esa)], ['156'])).
% 0.83/1.07  thf('221', plain,
% 0.83/1.07      (~
% 0.83/1.07       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.07          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.07          = (k2_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sat_resolution*', [status(thm)], ['219', '220'])).
% 0.83/1.07  thf('222', plain,
% 0.83/1.07      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.83/1.07      inference('simpl_trail', [status(thm)], ['178', '221'])).
% 0.83/1.07  thf('223', plain,
% 0.83/1.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.07        (k1_zfmisc_1 @ 
% 0.83/1.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.83/1.07  thf('224', plain,
% 0.83/1.07      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/1.07         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.83/1.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.07  thf('225', plain,
% 0.83/1.07      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.83/1.07         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['223', '224'])).
% 0.83/1.07  thf('226', plain,
% 0.83/1.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.83/1.07      inference('demod', [status(thm)], ['222', '225'])).
% 0.83/1.07  thf('227', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.83/1.07        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['153', '226'])).
% 0.83/1.07  thf('228', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.83/1.07      inference('simplify', [status(thm)], ['227'])).
% 0.83/1.07  thf('229', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('230', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.83/1.07      inference('demod', [status(thm)], ['61', '228', '229'])).
% 0.83/1.07  thf('231', plain,
% 0.83/1.07      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.83/1.07  thf('232', plain, (((sk_C) = (k1_xboole_0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['230', '231'])).
% 0.83/1.07  thf('233', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['213', '216'])).
% 0.83/1.07  thf('234', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('235', plain, ($false),
% 0.83/1.07      inference('demod', [status(thm)], ['10', '232', '233', '234'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.83/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
