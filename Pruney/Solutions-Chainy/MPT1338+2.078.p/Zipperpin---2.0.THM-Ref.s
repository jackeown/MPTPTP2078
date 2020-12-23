%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.03tRuoVNPD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  247 (6107 expanded)
%              Number of leaves         :   37 (1784 expanded)
%              Depth                    :   35
%              Number of atoms          : 2218 (150424 expanded)
%              Number of equality atoms :  136 (7539 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf('0',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','33'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','41','44','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','41','44','50'])).

thf('53',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','33'])).

thf('61',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('71',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','71'])).

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

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75','82','83','88'])).

thf('90',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('96',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','51','52','94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','71'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('105',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('106',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('108',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('110',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('117',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( v1_partfun1 @ X18 @ X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('118',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v4_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
      | ( v1_partfun1 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('125',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('129',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','125','126','127','128'])).

thf('130',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['107','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('138',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('139',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','139'])).

thf('141',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('143',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('151',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('155',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['163','168'])).

thf('170',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('174',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','161','162','176'])).

thf('178',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('182',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('183',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('190',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','190'])).

thf('192',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('193',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('196',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('197',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','197'])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','198'])).

thf('200',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('202',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['200','201'])).

thf('203',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['96','202'])).

thf('204',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('205',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('206',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','206'])).

thf('208',plain,(
    $false ),
    inference(simplify,[status(thm)],['207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.03tRuoVNPD
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 317 iterations in 0.111s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.58  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.58  thf(t62_tops_2, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.58                 ( m1_subset_1 @
% 0.21/0.58                   C @ 
% 0.21/0.58                   ( k1_zfmisc_1 @
% 0.21/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.58               ( ( ( ( k2_relset_1 @
% 0.21/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.21/0.58                 ( ( ( k1_relset_1 @
% 0.21/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.58                       ( k2_tops_2 @
% 0.21/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.58                   ( ( k2_relset_1 @
% 0.21/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.58                       ( k2_tops_2 @
% 0.21/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.58                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( l1_struct_0 @ A ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.58              ( ![C:$i]:
% 0.21/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.58                    ( v1_funct_2 @
% 0.21/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.58                    ( m1_subset_1 @
% 0.21/0.58                      C @ 
% 0.21/0.58                      ( k1_zfmisc_1 @
% 0.21/0.58                        ( k2_zfmisc_1 @
% 0.21/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.58                  ( ( ( ( k2_relset_1 @
% 0.21/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.58                      ( v2_funct_1 @ C ) ) =>
% 0.21/0.58                    ( ( ( k1_relset_1 @
% 0.21/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.58                          ( k2_tops_2 @
% 0.21/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.58                      ( ( k2_relset_1 @
% 0.21/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.58                          ( k2_tops_2 @
% 0.21/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.58                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_struct_0 @ sk_B))
% 0.21/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58            != (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf(d3_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.21/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('11', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.58  thf(cc5_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.58       ( ![C:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.58             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.21/0.58          | (v1_partfun1 @ X14 @ X15)
% 0.21/0.58          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.21/0.58          | ~ (v1_funct_1 @ X14)
% 0.21/0.58          | (v1_xboole_0 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '15', '22'])).
% 0.21/0.58  thf('24', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf(fc2_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X20 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.21/0.58          | ~ (l1_struct_0 @ X20)
% 0.21/0.58          | (v2_struct_0 @ X20))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '28'])).
% 0.21/0.58  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('33', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['23', '33'])).
% 0.21/0.58  thf(d4_partfun1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.58       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v1_partfun1 @ X18 @ X17)
% 0.21/0.58          | ((k1_relat_1 @ X18) = (X17))
% 0.21/0.58          | ~ (v4_relat_1 @ X18 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc2_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.58          | (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ 
% 0.21/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.21/0.58        | (v1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf(fc6_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.58         ((v4_relat_1 @ X5 @ X6)
% 0.21/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.58  thf('44', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.58  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t55_funct_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.58       ( ( v2_funct_1 @ A ) =>
% 0.21/0.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X4)
% 0.21/0.58          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.21/0.58          | ~ (v1_funct_1 @ X4)
% 0.21/0.58          | ~ (v1_relat_1 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '41', '44', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '41', '44', '50'])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.58  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('60', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['23', '33'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('63', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v1_partfun1 @ X18 @ X17)
% 0.21/0.58          | ((k1_relat_1 @ X18) = (X17))
% 0.21/0.58          | ~ (v4_relat_1 @ X18 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.58  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.58         ((v4_relat_1 @ X5 @ X6)
% 0.21/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.58  thf('69', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['58', '71'])).
% 0.21/0.58  thf(d4_tops_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.21/0.58          | ~ (v2_funct_1 @ X23)
% 0.21/0.58          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.21/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.21/0.58          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.21/0.58          | ~ (v1_funct_1 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.58  thf('74', plain,
% 0.21/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58             (u1_struct_0 @ sk_B))
% 0.21/0.58        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.58        | ((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (u1_struct_0 @ sk_B) @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.58  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['76', '77'])).
% 0.21/0.58  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58        (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.58  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.21/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.58  thf('87', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('88', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (u1_struct_0 @ sk_B) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      ((((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.21/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['74', '75', '82', '83', '88'])).
% 0.21/0.58  thf('90', plain,
% 0.21/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.58        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['53', '89'])).
% 0.21/0.58  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.58        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('simplify', [status(thm)], ['93'])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('96', plain,
% 0.21/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58          != (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['1', '51', '52', '94', '95'])).
% 0.21/0.58  thf('97', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['58', '71'])).
% 0.21/0.58  thf(dt_k2_tops_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.21/0.58         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.21/0.58           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.21/0.58  thf('98', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.58         ((m1_subset_1 @ (k2_tops_2 @ X24 @ X25 @ X26) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.21/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.58          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.21/0.58          | ~ (v1_funct_1 @ X26))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.58  thf('99', plain,
% 0.21/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58             (u1_struct_0 @ sk_B))
% 0.21/0.58        | (m1_subset_1 @ 
% 0.21/0.58           (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ 
% 0.21/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58             (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.58  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('101', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58        (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.58  thf('102', plain,
% 0.21/0.58      ((m1_subset_1 @ 
% 0.21/0.58        (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('simplify', [status(thm)], ['93'])).
% 0.21/0.58  thf('104', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('105', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X4)
% 0.21/0.58          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.21/0.58          | ~ (v1_funct_1 @ X4)
% 0.21/0.58          | ~ (v1_relat_1 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf('108', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.58  thf('110', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.58         ((v4_relat_1 @ X5 @ X6)
% 0.21/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.58  thf('112', plain,
% 0.21/0.58      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['108', '111'])).
% 0.21/0.58  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('115', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.21/0.58  thf('116', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X4)
% 0.21/0.58          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.21/0.58          | ~ (v1_funct_1 @ X4)
% 0.21/0.58          | ~ (v1_relat_1 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf('117', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (((k1_relat_1 @ X18) != (X17))
% 0.21/0.58          | (v1_partfun1 @ X18 @ X17)
% 0.21/0.58          | ~ (v4_relat_1 @ X18 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.58  thf('118', plain,
% 0.21/0.58      (![X18 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X18)
% 0.21/0.58          | ~ (v4_relat_1 @ X18 @ (k1_relat_1 @ X18))
% 0.21/0.58          | (v1_partfun1 @ X18 @ (k1_relat_1 @ X18)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['117'])).
% 0.21/0.58  thf('119', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['116', '118'])).
% 0.21/0.58  thf('120', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['115', '119'])).
% 0.21/0.58  thf('121', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.58  thf('122', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.58          | (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.58  thf('123', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ 
% 0.21/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58            (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.21/0.58        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.58  thf('124', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('125', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.21/0.58  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('129', plain,
% 0.21/0.58      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['120', '125', '126', '127', '128'])).
% 0.21/0.58  thf('130', plain,
% 0.21/0.58      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup+', [status(thm)], ['107', '129'])).
% 0.21/0.58  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('134', plain,
% 0.21/0.58      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.21/0.58  thf('135', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v1_partfun1 @ X18 @ X17)
% 0.21/0.58          | ((k1_relat_1 @ X18) = (X17))
% 0.21/0.58          | ~ (v4_relat_1 @ X18 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.58  thf('136', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['134', '135'])).
% 0.21/0.58  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.21/0.58  thf('138', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.21/0.58  thf('139', plain,
% 0.21/0.58      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.21/0.58  thf('140', plain,
% 0.21/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58         = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['106', '139'])).
% 0.21/0.58  thf('141', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('142', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('143', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['141', '142'])).
% 0.21/0.58  thf('144', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('145', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['143', '144'])).
% 0.21/0.58  thf('146', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('147', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.58      inference('demod', [status(thm)], ['145', '146'])).
% 0.21/0.58  thf('148', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('149', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (k2_relat_1 @ sk_C))))),
% 0.21/0.58      inference('demod', [status(thm)], ['147', '148'])).
% 0.21/0.58  thf('150', plain,
% 0.21/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.21/0.58          | ~ (v2_funct_1 @ X23)
% 0.21/0.58          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.21/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.21/0.58          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.21/0.58          | ~ (v1_funct_1 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.58  thf('151', plain,
% 0.21/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58             (k2_relat_1 @ sk_C))
% 0.21/0.58        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.58        | ((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['149', '150'])).
% 0.21/0.58  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('153', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('154', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.58  thf('155', plain,
% 0.21/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['153', '154'])).
% 0.21/0.58  thf('156', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('157', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['155', '156'])).
% 0.21/0.58  thf('158', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('159', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['157', '158'])).
% 0.21/0.58  thf('160', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('161', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58        (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['159', '160'])).
% 0.21/0.58  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('163', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('164', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('165', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('166', plain,
% 0.21/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58          = (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['164', '165'])).
% 0.21/0.58  thf('167', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('168', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['166', '167'])).
% 0.21/0.58  thf('169', plain,
% 0.21/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58          = (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['163', '168'])).
% 0.21/0.58  thf('170', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('171', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['169', '170'])).
% 0.21/0.58  thf('172', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('173', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('174', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.58         = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.21/0.58  thf('175', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('176', plain,
% 0.21/0.58      (((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['174', '175'])).
% 0.21/0.58  thf('177', plain,
% 0.21/0.58      ((((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.21/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['151', '152', '161', '162', '176'])).
% 0.21/0.58  thf('178', plain,
% 0.21/0.58      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58         (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('simplify', [status(thm)], ['177'])).
% 0.21/0.58  thf('179', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('180', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('181', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('182', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_struct_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('183', plain,
% 0.21/0.58      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58           != (k2_struct_0 @ sk_B))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['181', '182'])).
% 0.21/0.58  thf('184', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('185', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_struct_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['183', '184'])).
% 0.21/0.58  thf('186', plain,
% 0.21/0.58      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58           != (k2_struct_0 @ sk_B))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['180', '185'])).
% 0.21/0.58  thf('187', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('188', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_struct_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['186', '187'])).
% 0.21/0.58  thf('189', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('190', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          != (k2_relat_1 @ sk_C)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['188', '189'])).
% 0.21/0.58  thf('191', plain,
% 0.21/0.58      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58           != (k2_relat_1 @ sk_C))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['179', '190'])).
% 0.21/0.58  thf('192', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('193', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('194', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.21/0.58          != (k2_relat_1 @ sk_C)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.21/0.58  thf('195', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('196', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.21/0.58  thf('197', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58          (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58           (k2_relat_1 @ sk_C) @ sk_C))
% 0.21/0.58          != (k2_relat_1 @ sk_C)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.21/0.58  thf('198', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58          != (k2_relat_1 @ sk_C)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['178', '197'])).
% 0.21/0.58  thf('199', plain,
% 0.21/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58                = (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['140', '198'])).
% 0.21/0.58  thf('200', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          = (k2_struct_0 @ sk_B)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['199'])).
% 0.21/0.58  thf('201', plain,
% 0.21/0.58      (~
% 0.21/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          = (k2_struct_0 @ sk_A))) | 
% 0.21/0.58       ~
% 0.21/0.58       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          = (k2_struct_0 @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('202', plain,
% 0.21/0.58      (~
% 0.21/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.58          = (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['200', '201'])).
% 0.21/0.58  thf('203', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58         != (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['96', '202'])).
% 0.21/0.58  thf('204', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.58  thf('205', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.21/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('206', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.21/0.58         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['204', '205'])).
% 0.21/0.58  thf('207', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58         != (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['203', '206'])).
% 0.21/0.58  thf('208', plain, ($false), inference('simplify', [status(thm)], ['207'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
