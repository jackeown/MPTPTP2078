%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:01 EST 2020

% Result     : Theorem 44.63s
% Output     : CNFRefutation 44.71s
% Verified   : 
% Statistics : Number of formulae       :  211 (2107 expanded)
%              Number of leaves         :   49 ( 729 expanded)
%              Depth                    :   26
%              Number of atoms          :  567 (7830 expanded)
%              Number of equality atoms :   73 ( 605 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_158,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_187,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_16,plain,(
    ! [A_13] : ~ v1_subset_1('#skF_2'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1('#skF_2'(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58745,plain,(
    ! [B_2115,A_2116] :
      ( v1_subset_1(B_2115,A_2116)
      | B_2115 = A_2116
      | ~ m1_subset_1(B_2115,k1_zfmisc_1(A_2116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58748,plain,(
    ! [A_13] :
      ( v1_subset_1('#skF_2'(A_13),A_13)
      | '#skF_2'(A_13) = A_13 ) ),
    inference(resolution,[status(thm)],[c_18,c_58745])).

tff(c_58754,plain,(
    ! [A_13] : '#skF_2'(A_13) = A_13 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_58748])).

tff(c_58758,plain,(
    ! [A_13] : ~ v1_subset_1(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58754,c_16])).

tff(c_58757,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58754,c_18])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_59611,plain,(
    ! [A_2261,B_2262,C_2263] :
      ( r2_hidden('#skF_1'(A_2261,B_2262,C_2263),B_2262)
      | r2_hidden('#skF_1'(A_2261,B_2262,C_2263),C_2263)
      | C_2263 = B_2262
      | ~ m1_subset_1(C_2263,k1_zfmisc_1(A_2261))
      | ~ m1_subset_1(B_2262,k1_zfmisc_1(A_2261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67824,plain,(
    ! [A_2672,B_2673,C_2674,A_2675] :
      ( r2_hidden('#skF_1'(A_2672,B_2673,C_2674),A_2675)
      | ~ m1_subset_1(B_2673,k1_zfmisc_1(A_2675))
      | r2_hidden('#skF_1'(A_2672,B_2673,C_2674),C_2674)
      | C_2674 = B_2673
      | ~ m1_subset_1(C_2674,k1_zfmisc_1(A_2672))
      | ~ m1_subset_1(B_2673,k1_zfmisc_1(A_2672)) ) ),
    inference(resolution,[status(thm)],[c_59611,c_4])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74176,plain,(
    ! [A_2983,B_2984,C_2985,A_2986] :
      ( m1_subset_1('#skF_1'(A_2983,B_2984,C_2985),A_2986)
      | ~ m1_subset_1(B_2984,k1_zfmisc_1(A_2986))
      | r2_hidden('#skF_1'(A_2983,B_2984,C_2985),C_2985)
      | C_2985 = B_2984
      | ~ m1_subset_1(C_2985,k1_zfmisc_1(A_2983))
      | ~ m1_subset_1(B_2984,k1_zfmisc_1(A_2983)) ) ),
    inference(resolution,[status(thm)],[c_67824,c_20])).

tff(c_116431,plain,(
    ! [A_4138,B_4139,C_4140,A_4141] :
      ( m1_subset_1('#skF_1'(A_4138,B_4139,C_4140),C_4140)
      | m1_subset_1('#skF_1'(A_4138,B_4139,C_4140),A_4141)
      | ~ m1_subset_1(B_4139,k1_zfmisc_1(A_4141))
      | C_4140 = B_4139
      | ~ m1_subset_1(C_4140,k1_zfmisc_1(A_4138))
      | ~ m1_subset_1(B_4139,k1_zfmisc_1(A_4138)) ) ),
    inference(resolution,[status(thm)],[c_74176,c_20])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58785,plain,(
    ! [C_2124,A_2125,B_2126] :
      ( r2_hidden(C_2124,A_2125)
      | ~ r2_hidden(C_2124,B_2126)
      | ~ m1_subset_1(B_2126,k1_zfmisc_1(A_2125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58822,plain,(
    ! [A_2132,A_2133,B_2134] :
      ( r2_hidden(A_2132,A_2133)
      | ~ m1_subset_1(B_2134,k1_zfmisc_1(A_2133))
      | v1_xboole_0(B_2134)
      | ~ m1_subset_1(A_2132,B_2134) ) ),
    inference(resolution,[status(thm)],[c_22,c_58785])).

tff(c_58829,plain,(
    ! [A_2132] :
      ( r2_hidden(A_2132,u1_struct_0('#skF_7'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_2132,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_58822])).

tff(c_58834,plain,(
    ! [A_2132] :
      ( r2_hidden(A_2132,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_2132,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_58829])).

tff(c_80,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58835,plain,(
    ! [A_2135] :
      ( r2_hidden(A_2135,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_2135,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_58829])).

tff(c_58845,plain,(
    ! [A_2135] :
      ( m1_subset_1(A_2135,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_2135,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58835,c_20])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58968,plain,(
    ! [A_2159,B_2160,C_2161] :
      ( r2_hidden('#skF_3'(A_2159,B_2160,C_2161),B_2160)
      | r2_lattice3(A_2159,B_2160,C_2161)
      | ~ m1_subset_1(C_2161,u1_struct_0(A_2159))
      | ~ l1_orders_2(A_2159) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59007,plain,(
    ! [B_2167,A_2168,C_2169] :
      ( ~ r1_tarski(B_2167,'#skF_3'(A_2168,B_2167,C_2169))
      | r2_lattice3(A_2168,B_2167,C_2169)
      | ~ m1_subset_1(C_2169,u1_struct_0(A_2168))
      | ~ l1_orders_2(A_2168) ) ),
    inference(resolution,[status(thm)],[c_58968,c_26])).

tff(c_59028,plain,(
    ! [A_2171,C_2172] :
      ( r2_lattice3(A_2171,k1_xboole_0,C_2172)
      | ~ m1_subset_1(C_2172,u1_struct_0(A_2171))
      | ~ l1_orders_2(A_2171) ) ),
    inference(resolution,[status(thm)],[c_2,c_59007])).

tff(c_59048,plain,(
    ! [A_2135] :
      ( r2_lattice3('#skF_7',k1_xboole_0,A_2135)
      | ~ l1_orders_2('#skF_7')
      | ~ m1_subset_1(A_2135,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58845,c_59028])).

tff(c_59072,plain,(
    ! [A_2135] :
      ( r2_lattice3('#skF_7',k1_xboole_0,A_2135)
      | ~ m1_subset_1(A_2135,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_59048])).

tff(c_74,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_122,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,B_94)
      | v1_xboole_0(B_94)
      | ~ m1_subset_1(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_115,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_125,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_122,c_115])).

tff(c_134,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_125])).

tff(c_92,plain,
    ( r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
    | ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_137,plain,(
    ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_92])).

tff(c_145,plain,(
    ! [B_98,A_99] :
      ( v1_subset_1(B_98,A_99)
      | B_98 = A_99
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_151,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_72,c_145])).

tff(c_157,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_151])).

tff(c_105,plain,(
    ! [A_89] :
      ( k1_yellow_0(A_89,k1_xboole_0) = k3_yellow_0(A_89)
      | ~ l1_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_109,plain,(
    k1_yellow_0('#skF_7',k1_xboole_0) = k3_yellow_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_105])).

tff(c_116,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k1_yellow_0(A_91,B_92),u1_struct_0(A_91))
      | ~ l1_orders_2(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_119,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_116])).

tff(c_121,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_119])).

tff(c_171,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_121])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_171])).

tff(c_176,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_187,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k1_yellow_0(A_102,B_103),u1_struct_0(A_102))
      | ~ l1_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_190,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_187])).

tff(c_192,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_190])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_84,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_82,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    ! [A_52] :
      ( r1_yellow_0(A_52,k1_xboole_0)
      | ~ l1_orders_2(A_52)
      | ~ v1_yellow_0(A_52)
      | ~ v5_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_60639,plain,(
    ! [A_2344,B_2345,D_2346] :
      ( r1_orders_2(A_2344,k1_yellow_0(A_2344,B_2345),D_2346)
      | ~ r2_lattice3(A_2344,B_2345,D_2346)
      | ~ m1_subset_1(D_2346,u1_struct_0(A_2344))
      | ~ r1_yellow_0(A_2344,B_2345)
      | ~ m1_subset_1(k1_yellow_0(A_2344,B_2345),u1_struct_0(A_2344))
      | ~ l1_orders_2(A_2344) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60649,plain,(
    ! [D_2346] :
      ( r1_orders_2('#skF_7',k1_yellow_0('#skF_7',k1_xboole_0),D_2346)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2346)
      | ~ m1_subset_1(D_2346,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_60639])).

tff(c_60658,plain,(
    ! [D_2346] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),D_2346)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2346)
      | ~ m1_subset_1(D_2346,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_192,c_109,c_60649])).

tff(c_60659,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_60658])).

tff(c_60662,plain,
    ( ~ l1_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_60659])).

tff(c_60665,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_60662])).

tff(c_60667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_60665])).

tff(c_60668,plain,(
    ! [D_2346] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),D_2346)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2346)
      | ~ m1_subset_1(D_2346,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_60658])).

tff(c_60712,plain,(
    ! [D_2359,B_2360,A_2361,C_2362] :
      ( r2_hidden(D_2359,B_2360)
      | ~ r1_orders_2(A_2361,C_2362,D_2359)
      | ~ r2_hidden(C_2362,B_2360)
      | ~ m1_subset_1(D_2359,u1_struct_0(A_2361))
      | ~ m1_subset_1(C_2362,u1_struct_0(A_2361))
      | ~ v13_waybel_0(B_2360,A_2361)
      | ~ m1_subset_1(B_2360,k1_zfmisc_1(u1_struct_0(A_2361)))
      | ~ l1_orders_2(A_2361) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60716,plain,(
    ! [D_2346,B_2360] :
      ( r2_hidden(D_2346,B_2360)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_2360)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_2360,'#skF_7')
      | ~ m1_subset_1(B_2360,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2346)
      | ~ m1_subset_1(D_2346,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_60668,c_60712])).

tff(c_68603,plain,(
    ! [D_2708,B_2709] :
      ( r2_hidden(D_2708,B_2709)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_2709)
      | ~ v13_waybel_0(B_2709,'#skF_7')
      | ~ m1_subset_1(B_2709,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2708)
      | ~ m1_subset_1(D_2708,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_192,c_60716])).

tff(c_68656,plain,(
    ! [D_2708] :
      ( r2_hidden(D_2708,'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2708)
      | ~ m1_subset_1(D_2708,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_72,c_68603])).

tff(c_68679,plain,(
    ! [D_2710] :
      ( r2_hidden(D_2710,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2710)
      | ~ m1_subset_1(D_2710,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_176,c_68656])).

tff(c_68831,plain,(
    ! [A_2711] :
      ( r2_hidden(A_2711,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,A_2711)
      | ~ m1_subset_1(A_2711,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58845,c_68679])).

tff(c_68942,plain,(
    ! [A_2712] :
      ( r2_hidden(A_2712,'#skF_8')
      | ~ m1_subset_1(A_2712,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_59072,c_68831])).

tff(c_8,plain,(
    ! [A_6,B_7,C_11] :
      ( ~ r2_hidden('#skF_1'(A_6,B_7,C_11),C_11)
      | ~ r2_hidden('#skF_1'(A_6,B_7,C_11),B_7)
      | C_11 = B_7
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72166,plain,(
    ! [A_2911,B_2912] :
      ( ~ r2_hidden('#skF_1'(A_2911,B_2912,'#skF_8'),B_2912)
      | B_2912 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_2911))
      | ~ m1_subset_1(B_2912,k1_zfmisc_1(A_2911))
      | ~ m1_subset_1('#skF_1'(A_2911,B_2912,'#skF_8'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68942,c_8])).

tff(c_72256,plain,(
    ! [A_2911] :
      ( u1_struct_0('#skF_7') = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_2911))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2911))
      | ~ m1_subset_1('#skF_1'(A_2911,u1_struct_0('#skF_7'),'#skF_8'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58834,c_72166])).

tff(c_72258,plain,(
    ! [A_2911] :
      ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_2911))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2911))
      | ~ m1_subset_1('#skF_1'(A_2911,u1_struct_0('#skF_7'),'#skF_8'),'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_72256])).

tff(c_117196,plain,(
    ! [A_4138,A_4141] :
      ( m1_subset_1('#skF_1'(A_4138,u1_struct_0('#skF_7'),'#skF_8'),A_4141)
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4141))
      | u1_struct_0('#skF_7') = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_4138))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4138)) ) ),
    inference(resolution,[status(thm)],[c_116431,c_72258])).

tff(c_117365,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_117196])).

tff(c_58777,plain,(
    ! [A_2120,C_2121,B_2122] :
      ( m1_subset_1(A_2120,C_2121)
      | ~ m1_subset_1(B_2122,k1_zfmisc_1(C_2121))
      | ~ r2_hidden(A_2120,B_2122) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58783,plain,(
    ! [A_2120] :
      ( m1_subset_1(A_2120,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_2120,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_58777])).

tff(c_59659,plain,(
    ! [A_2261,B_2262,C_2263,A_2] :
      ( r2_hidden('#skF_1'(A_2261,B_2262,C_2263),A_2)
      | ~ m1_subset_1(C_2263,k1_zfmisc_1(A_2))
      | r2_hidden('#skF_1'(A_2261,B_2262,C_2263),B_2262)
      | C_2263 = B_2262
      | ~ m1_subset_1(C_2263,k1_zfmisc_1(A_2261))
      | ~ m1_subset_1(B_2262,k1_zfmisc_1(A_2261)) ) ),
    inference(resolution,[status(thm)],[c_59611,c_4])).

tff(c_67655,plain,(
    ! [C_2661,A_2662,A_2663] :
      ( ~ m1_subset_1(C_2661,k1_zfmisc_1(A_2662))
      | C_2661 = A_2662
      | ~ m1_subset_1(C_2661,k1_zfmisc_1(A_2663))
      | ~ m1_subset_1(A_2662,k1_zfmisc_1(A_2663))
      | r2_hidden('#skF_1'(A_2663,A_2662,C_2661),A_2662) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_59659])).

tff(c_59462,plain,(
    ! [A_2241,B_2242,C_2243] :
      ( ~ r2_hidden('#skF_1'(A_2241,B_2242,C_2243),C_2243)
      | ~ r2_hidden('#skF_1'(A_2241,B_2242,C_2243),B_2242)
      | C_2243 = B_2242
      | ~ m1_subset_1(C_2243,k1_zfmisc_1(A_2241))
      | ~ m1_subset_1(B_2242,k1_zfmisc_1(A_2241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59470,plain,(
    ! [A_2241,B_2242,B_18] :
      ( ~ r2_hidden('#skF_1'(A_2241,B_2242,B_18),B_2242)
      | B_2242 = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_2241))
      | ~ m1_subset_1(B_2242,k1_zfmisc_1(A_2241))
      | v1_xboole_0(B_18)
      | ~ m1_subset_1('#skF_1'(A_2241,B_2242,B_18),B_18) ) ),
    inference(resolution,[status(thm)],[c_22,c_59462])).

tff(c_68297,plain,(
    ! [C_2693,A_2694,A_2695] :
      ( v1_xboole_0(C_2693)
      | ~ m1_subset_1('#skF_1'(A_2694,A_2695,C_2693),C_2693)
      | ~ m1_subset_1(C_2693,k1_zfmisc_1(A_2695))
      | C_2693 = A_2695
      | ~ m1_subset_1(C_2693,k1_zfmisc_1(A_2694))
      | ~ m1_subset_1(A_2695,k1_zfmisc_1(A_2694)) ) ),
    inference(resolution,[status(thm)],[c_67655,c_59470])).

tff(c_68363,plain,(
    ! [A_2695,A_2694] :
      ( v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2695))
      | u1_struct_0('#skF_7') = A_2695
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2694))
      | ~ m1_subset_1(A_2695,k1_zfmisc_1(A_2694))
      | ~ r2_hidden('#skF_1'(A_2694,A_2695,u1_struct_0('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58783,c_68297])).

tff(c_68602,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_68363])).

tff(c_117553,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117365,c_68602])).

tff(c_117596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_117553])).

tff(c_117598,plain,(
    u1_struct_0('#skF_7') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_117196])).

tff(c_6,plain,(
    ! [A_6,B_7,C_11] :
      ( m1_subset_1('#skF_1'(A_6,B_7,C_11),A_6)
      | C_11 = B_7
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59067,plain,(
    ! [A_2171,B_7,C_11] :
      ( r2_lattice3(A_2171,k1_xboole_0,'#skF_1'(u1_struct_0(A_2171),B_7,C_11))
      | ~ l1_orders_2(A_2171)
      | C_11 = B_7
      | ~ m1_subset_1(C_11,k1_zfmisc_1(u1_struct_0(A_2171)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_2171))) ) ),
    inference(resolution,[status(thm)],[c_6,c_59028])).

tff(c_118036,plain,(
    ! [A_4146,A_4147] :
      ( m1_subset_1('#skF_1'(A_4146,u1_struct_0('#skF_7'),'#skF_8'),A_4147)
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4147))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_4146))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4146)) ) ),
    inference(splitRight,[status(thm)],[c_117196])).

tff(c_68678,plain,(
    ! [D_2708] :
      ( r2_hidden(D_2708,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_2708)
      | ~ m1_subset_1(D_2708,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_176,c_68656])).

tff(c_118294,plain,(
    ! [A_4146] :
      ( r2_hidden('#skF_1'(A_4146,u1_struct_0('#skF_7'),'#skF_8'),'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(A_4146,u1_struct_0('#skF_7'),'#skF_8'))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_4146))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4146)) ) ),
    inference(resolution,[status(thm)],[c_118036,c_68678])).

tff(c_118553,plain,(
    ! [A_4148] :
      ( r2_hidden('#skF_1'(A_4148,u1_struct_0('#skF_7'),'#skF_8'),'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(A_4148,u1_struct_0('#skF_7'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_4148))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_4148)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_118294])).

tff(c_118589,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),'#skF_8'),'#skF_8')
    | ~ l1_orders_2('#skF_7')
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_59067,c_118553])).

tff(c_118628,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),'#skF_8'),'#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_72,c_80,c_118589])).

tff(c_118629,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_117598,c_118628])).

tff(c_118657,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),'#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_118629,c_20])).

tff(c_67375,plain,(
    ! [A_2653,B_2654,C_2655,A_2656] :
      ( r2_hidden('#skF_1'(A_2653,B_2654,C_2655),A_2656)
      | ~ m1_subset_1(C_2655,k1_zfmisc_1(A_2656))
      | r2_hidden('#skF_1'(A_2653,B_2654,C_2655),B_2654)
      | C_2655 = B_2654
      | ~ m1_subset_1(C_2655,k1_zfmisc_1(A_2653))
      | ~ m1_subset_1(B_2654,k1_zfmisc_1(A_2653)) ) ),
    inference(resolution,[status(thm)],[c_59611,c_4])).

tff(c_80100,plain,(
    ! [B_3189,A_3190,A_3188,A_3187,C_3191] :
      ( r2_hidden('#skF_1'(A_3188,B_3189,C_3191),A_3190)
      | ~ m1_subset_1(A_3187,k1_zfmisc_1(A_3190))
      | ~ m1_subset_1(C_3191,k1_zfmisc_1(A_3187))
      | r2_hidden('#skF_1'(A_3188,B_3189,C_3191),B_3189)
      | C_3191 = B_3189
      | ~ m1_subset_1(C_3191,k1_zfmisc_1(A_3188))
      | ~ m1_subset_1(B_3189,k1_zfmisc_1(A_3188)) ) ),
    inference(resolution,[status(thm)],[c_67375,c_4])).

tff(c_80222,plain,(
    ! [A_3188,B_3189,C_3191] :
      ( r2_hidden('#skF_1'(A_3188,B_3189,C_3191),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_3191,k1_zfmisc_1('#skF_8'))
      | r2_hidden('#skF_1'(A_3188,B_3189,C_3191),B_3189)
      | C_3191 = B_3189
      | ~ m1_subset_1(C_3191,k1_zfmisc_1(A_3188))
      | ~ m1_subset_1(B_3189,k1_zfmisc_1(A_3188)) ) ),
    inference(resolution,[status(thm)],[c_72,c_80100])).

tff(c_81970,plain,(
    ! [C_3227,A_3228] :
      ( ~ m1_subset_1(C_3227,k1_zfmisc_1('#skF_8'))
      | u1_struct_0('#skF_7') = C_3227
      | ~ m1_subset_1(C_3227,k1_zfmisc_1(A_3228))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_3228))
      | r2_hidden('#skF_1'(A_3228,u1_struct_0('#skF_7'),C_3227),u1_struct_0('#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_80222])).

tff(c_82012,plain,(
    ! [C_3227,A_3228] :
      ( v1_xboole_0(C_3227)
      | ~ m1_subset_1('#skF_1'(A_3228,u1_struct_0('#skF_7'),C_3227),C_3227)
      | ~ m1_subset_1(C_3227,k1_zfmisc_1('#skF_8'))
      | u1_struct_0('#skF_7') = C_3227
      | ~ m1_subset_1(C_3227,k1_zfmisc_1(A_3228))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_3228)) ) ),
    inference(resolution,[status(thm)],[c_81970,c_59470])).

tff(c_118661,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_118657,c_82012])).

tff(c_118687,plain,
    ( v1_xboole_0('#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_72,c_58757,c_118661])).

tff(c_118689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117598,c_78,c_118687])).

tff(c_118690,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72256])).

tff(c_118722,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118690,c_68602])).

tff(c_118774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_118722])).

tff(c_118776,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68363])).

tff(c_60292,plain,(
    ! [A_2320,B_2321,C_2322] :
      ( m1_subset_1('#skF_1'(A_2320,B_2321,C_2322),B_2321)
      | r2_hidden('#skF_1'(A_2320,B_2321,C_2322),C_2322)
      | C_2322 = B_2321
      | ~ m1_subset_1(C_2322,k1_zfmisc_1(A_2320))
      | ~ m1_subset_1(B_2321,k1_zfmisc_1(A_2320)) ) ),
    inference(resolution,[status(thm)],[c_59611,c_20])).

tff(c_60390,plain,(
    ! [A_2320,B_2321,C_2322] :
      ( m1_subset_1('#skF_1'(A_2320,B_2321,C_2322),C_2322)
      | m1_subset_1('#skF_1'(A_2320,B_2321,C_2322),B_2321)
      | C_2322 = B_2321
      | ~ m1_subset_1(C_2322,k1_zfmisc_1(A_2320))
      | ~ m1_subset_1(B_2321,k1_zfmisc_1(A_2320)) ) ),
    inference(resolution,[status(thm)],[c_60292,c_20])).

tff(c_118806,plain,(
    ! [D_4152,B_4153] :
      ( r2_hidden(D_4152,B_4153)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_4153)
      | ~ v13_waybel_0(B_4153,'#skF_7')
      | ~ m1_subset_1(B_4153,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_4152)
      | ~ m1_subset_1(D_4152,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_192,c_60716])).

tff(c_118859,plain,(
    ! [D_4152] :
      ( r2_hidden(D_4152,'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_4152)
      | ~ m1_subset_1(D_4152,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_72,c_118806])).

tff(c_118882,plain,(
    ! [D_4154] :
      ( r2_hidden(D_4154,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_4154)
      | ~ m1_subset_1(D_4154,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_176,c_118859])).

tff(c_119067,plain,(
    ! [A_4157] :
      ( r2_hidden(A_4157,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,A_4157)
      | ~ m1_subset_1(A_4157,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58845,c_118882])).

tff(c_119170,plain,(
    ! [A_2135] :
      ( r2_hidden(A_2135,'#skF_8')
      | ~ m1_subset_1(A_2135,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_59072,c_119067])).

tff(c_67931,plain,(
    ! [A_2672,B_2673,C_2674,A_2675] :
      ( m1_subset_1('#skF_1'(A_2672,B_2673,C_2674),A_2675)
      | ~ m1_subset_1(B_2673,k1_zfmisc_1(A_2675))
      | r2_hidden('#skF_1'(A_2672,B_2673,C_2674),C_2674)
      | C_2674 = B_2673
      | ~ m1_subset_1(C_2674,k1_zfmisc_1(A_2672))
      | ~ m1_subset_1(B_2673,k1_zfmisc_1(A_2672)) ) ),
    inference(resolution,[status(thm)],[c_67824,c_20])).

tff(c_61561,plain,(
    ! [A_2404,B_2405,B_2406] :
      ( ~ r2_hidden('#skF_1'(A_2404,B_2405,B_2406),B_2405)
      | B_2406 = B_2405
      | ~ m1_subset_1(B_2406,k1_zfmisc_1(A_2404))
      | ~ m1_subset_1(B_2405,k1_zfmisc_1(A_2404))
      | v1_xboole_0(B_2406)
      | ~ m1_subset_1('#skF_1'(A_2404,B_2405,B_2406),B_2406) ) ),
    inference(resolution,[status(thm)],[c_22,c_59462])).

tff(c_121099,plain,(
    ! [B_4287,B_4286,A_4288] :
      ( B_4287 = B_4286
      | ~ m1_subset_1(B_4286,k1_zfmisc_1(A_4288))
      | ~ m1_subset_1(B_4287,k1_zfmisc_1(A_4288))
      | v1_xboole_0(B_4286)
      | ~ m1_subset_1('#skF_1'(A_4288,B_4287,B_4286),B_4286)
      | v1_xboole_0(B_4287)
      | ~ m1_subset_1('#skF_1'(A_4288,B_4287,B_4286),B_4287) ) ),
    inference(resolution,[status(thm)],[c_22,c_61561])).

tff(c_121124,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(A_6)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1('#skF_1'(A_6,B_7,A_6),B_7)
      | B_7 = A_6
      | ~ m1_subset_1(A_6,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_6,c_121099])).

tff(c_121589,plain,(
    ! [A_4301,B_4302] :
      ( v1_xboole_0(A_4301)
      | v1_xboole_0(B_4302)
      | ~ m1_subset_1('#skF_1'(A_4301,B_4302,A_4301),B_4302)
      | B_4302 = A_4301
      | ~ m1_subset_1(B_4302,k1_zfmisc_1(A_4301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_121124])).

tff(c_121593,plain,(
    ! [C_2674,A_2675] :
      ( v1_xboole_0(C_2674)
      | v1_xboole_0(A_2675)
      | ~ m1_subset_1(A_2675,k1_zfmisc_1(A_2675))
      | r2_hidden('#skF_1'(C_2674,A_2675,C_2674),C_2674)
      | C_2674 = A_2675
      | ~ m1_subset_1(C_2674,k1_zfmisc_1(C_2674))
      | ~ m1_subset_1(A_2675,k1_zfmisc_1(C_2674)) ) ),
    inference(resolution,[status(thm)],[c_67931,c_121589])).

tff(c_121680,plain,(
    ! [C_4303,A_4304] :
      ( v1_xboole_0(C_4303)
      | v1_xboole_0(A_4304)
      | r2_hidden('#skF_1'(C_4303,A_4304,C_4303),C_4303)
      | C_4303 = A_4304
      | ~ m1_subset_1(A_4304,k1_zfmisc_1(C_4303)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_58757,c_121593])).

tff(c_121723,plain,(
    ! [C_4303,A_4304] :
      ( ~ r2_hidden('#skF_1'(C_4303,A_4304,C_4303),A_4304)
      | ~ m1_subset_1(C_4303,k1_zfmisc_1(C_4303))
      | v1_xboole_0(C_4303)
      | v1_xboole_0(A_4304)
      | C_4303 = A_4304
      | ~ m1_subset_1(A_4304,k1_zfmisc_1(C_4303)) ) ),
    inference(resolution,[status(thm)],[c_121680,c_8])).

tff(c_122023,plain,(
    ! [C_4314,A_4315] :
      ( ~ r2_hidden('#skF_1'(C_4314,A_4315,C_4314),A_4315)
      | v1_xboole_0(C_4314)
      | v1_xboole_0(A_4315)
      | C_4314 = A_4315
      | ~ m1_subset_1(A_4315,k1_zfmisc_1(C_4314)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_121723])).

tff(c_122039,plain,(
    ! [C_4314] :
      ( v1_xboole_0(C_4314)
      | v1_xboole_0('#skF_8')
      | C_4314 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(C_4314))
      | ~ m1_subset_1('#skF_1'(C_4314,'#skF_8',C_4314),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_119170,c_122023])).

tff(c_122164,plain,(
    ! [C_4316] :
      ( v1_xboole_0(C_4316)
      | C_4316 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(C_4316))
      | ~ m1_subset_1('#skF_1'(C_4316,'#skF_8',C_4316),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_122039])).

tff(c_122184,plain,(
    ! [C_2322] :
      ( v1_xboole_0(C_2322)
      | m1_subset_1('#skF_1'(C_2322,'#skF_8',C_2322),C_2322)
      | C_2322 = '#skF_8'
      | ~ m1_subset_1(C_2322,k1_zfmisc_1(C_2322))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(C_2322)) ) ),
    inference(resolution,[status(thm)],[c_60390,c_122164])).

tff(c_122483,plain,(
    ! [C_4321] :
      ( v1_xboole_0(C_4321)
      | m1_subset_1('#skF_1'(C_4321,'#skF_8',C_4321),C_4321)
      | C_4321 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(C_4321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_122184])).

tff(c_118881,plain,(
    ! [D_4152] :
      ( r2_hidden(D_4152,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_4152)
      | ~ m1_subset_1(D_4152,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_176,c_118859])).

tff(c_122533,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')),'#skF_8')
    | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_122483,c_118881])).

tff(c_122650,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')),'#skF_8')
    | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122533])).

tff(c_122651,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')),'#skF_8')
    | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_118776,c_122650])).

tff(c_123214,plain,(
    ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_122651])).

tff(c_123217,plain,
    ( ~ l1_orders_2('#skF_7')
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_59067,c_123214])).

tff(c_123226,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58757,c_80,c_123217])).

tff(c_61989,plain,(
    ! [B_2428,A_2429] :
      ( u1_struct_0('#skF_7') = B_2428
      | ~ m1_subset_1(B_2428,k1_zfmisc_1(A_2429))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2429))
      | v1_xboole_0(B_2428)
      | ~ m1_subset_1('#skF_1'(A_2429,u1_struct_0('#skF_7'),B_2428),B_2428)
      | ~ m1_subset_1('#skF_1'(A_2429,u1_struct_0('#skF_7'),B_2428),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58834,c_61561])).

tff(c_62003,plain,(
    ! [A_6] :
      ( v1_xboole_0(A_6)
      | ~ m1_subset_1('#skF_1'(A_6,u1_struct_0('#skF_7'),A_6),'#skF_8')
      | u1_struct_0('#skF_7') = A_6
      | ~ m1_subset_1(A_6,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_6,c_61989])).

tff(c_67340,plain,(
    ! [A_2652] :
      ( v1_xboole_0(A_2652)
      | ~ m1_subset_1('#skF_1'(A_2652,u1_struct_0('#skF_7'),A_2652),'#skF_8')
      | u1_struct_0('#skF_7') = A_2652
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_2652)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_62003])).

tff(c_67352,plain,
    ( v1_xboole_0('#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_67340])).

tff(c_67358,plain,
    ( v1_xboole_0('#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_67352])).

tff(c_67359,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_67358])).

tff(c_67360,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_67359])).

tff(c_123543,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123226,c_67360])).

tff(c_123592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_123543])).

tff(c_123593,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | r2_hidden('#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_122651])).

tff(c_123620,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_7'),'#skF_8',u1_struct_0('#skF_7')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_123593])).

tff(c_121766,plain,(
    ! [C_4303,A_4304] :
      ( ~ r2_hidden('#skF_1'(C_4303,A_4304,C_4303),A_4304)
      | v1_xboole_0(C_4303)
      | v1_xboole_0(A_4304)
      | C_4303 = A_4304
      | ~ m1_subset_1(A_4304,k1_zfmisc_1(C_4303)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_121723])).

tff(c_123655,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | v1_xboole_0('#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_123620,c_121766])).

tff(c_123676,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | v1_xboole_0('#skF_8')
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_123655])).

tff(c_123677,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_118776,c_123676])).

tff(c_123732,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123677,c_67360])).

tff(c_123781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_123732])).

tff(c_123782,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_123593])).

tff(c_123822,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123782,c_67360])).

tff(c_123871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58757,c_123822])).

tff(c_123872,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_67359])).

tff(c_175,plain,(
    v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_123919,plain,(
    v1_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123872,c_175])).

tff(c_123925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58758,c_123919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.63/33.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.71/33.74  
% 44.71/33.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.71/33.74  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_5
% 44.71/33.74  
% 44.71/33.74  %Foreground sorts:
% 44.71/33.74  
% 44.71/33.74  
% 44.71/33.74  %Background operators:
% 44.71/33.74  
% 44.71/33.74  
% 44.71/33.74  %Foreground operators:
% 44.71/33.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 44.71/33.74  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 44.71/33.74  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 44.71/33.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 44.71/33.74  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 44.71/33.74  tff('#skF_2', type, '#skF_2': $i > $i).
% 44.71/33.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.71/33.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 44.71/33.74  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 44.71/33.74  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 44.71/33.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.71/33.74  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 44.71/33.74  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 44.71/33.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 44.71/33.74  tff('#skF_7', type, '#skF_7': $i).
% 44.71/33.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.71/33.74  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 44.71/33.74  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 44.71/33.74  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 44.71/33.74  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 44.71/33.74  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 44.71/33.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 44.71/33.74  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 44.71/33.74  tff('#skF_8', type, '#skF_8': $i).
% 44.71/33.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.71/33.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 44.71/33.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.71/33.74  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 44.71/33.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 44.71/33.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 44.71/33.74  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 44.71/33.74  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 44.71/33.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 44.71/33.74  
% 44.71/33.77  tff(f_54, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 44.71/33.77  tff(f_158, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 44.71/33.77  tff(f_187, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 44.71/33.77  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 44.71/33.77  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 44.71/33.77  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 44.71/33.77  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 44.71/33.77  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 44.71/33.77  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 44.71/33.77  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 44.71/33.77  tff(f_93, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 44.71/33.77  tff(f_115, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 44.71/33.77  tff(f_132, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 44.71/33.77  tff(f_111, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 44.71/33.77  tff(f_151, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 44.71/33.77  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 44.71/33.77  tff(c_16, plain, (![A_13]: (~v1_subset_1('#skF_2'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 44.71/33.77  tff(c_18, plain, (![A_13]: (m1_subset_1('#skF_2'(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 44.71/33.77  tff(c_58745, plain, (![B_2115, A_2116]: (v1_subset_1(B_2115, A_2116) | B_2115=A_2116 | ~m1_subset_1(B_2115, k1_zfmisc_1(A_2116)))), inference(cnfTransformation, [status(thm)], [f_158])).
% 44.71/33.77  tff(c_58748, plain, (![A_13]: (v1_subset_1('#skF_2'(A_13), A_13) | '#skF_2'(A_13)=A_13)), inference(resolution, [status(thm)], [c_18, c_58745])).
% 44.71/33.77  tff(c_58754, plain, (![A_13]: ('#skF_2'(A_13)=A_13)), inference(negUnitSimplification, [status(thm)], [c_16, c_58748])).
% 44.71/33.77  tff(c_58758, plain, (![A_13]: (~v1_subset_1(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_58754, c_16])).
% 44.71/33.77  tff(c_58757, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_58754, c_18])).
% 44.71/33.77  tff(c_78, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_59611, plain, (![A_2261, B_2262, C_2263]: (r2_hidden('#skF_1'(A_2261, B_2262, C_2263), B_2262) | r2_hidden('#skF_1'(A_2261, B_2262, C_2263), C_2263) | C_2263=B_2262 | ~m1_subset_1(C_2263, k1_zfmisc_1(A_2261)) | ~m1_subset_1(B_2262, k1_zfmisc_1(A_2261)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 44.71/33.77  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 44.71/33.77  tff(c_67824, plain, (![A_2672, B_2673, C_2674, A_2675]: (r2_hidden('#skF_1'(A_2672, B_2673, C_2674), A_2675) | ~m1_subset_1(B_2673, k1_zfmisc_1(A_2675)) | r2_hidden('#skF_1'(A_2672, B_2673, C_2674), C_2674) | C_2674=B_2673 | ~m1_subset_1(C_2674, k1_zfmisc_1(A_2672)) | ~m1_subset_1(B_2673, k1_zfmisc_1(A_2672)))), inference(resolution, [status(thm)], [c_59611, c_4])).
% 44.71/33.77  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 44.71/33.77  tff(c_74176, plain, (![A_2983, B_2984, C_2985, A_2986]: (m1_subset_1('#skF_1'(A_2983, B_2984, C_2985), A_2986) | ~m1_subset_1(B_2984, k1_zfmisc_1(A_2986)) | r2_hidden('#skF_1'(A_2983, B_2984, C_2985), C_2985) | C_2985=B_2984 | ~m1_subset_1(C_2985, k1_zfmisc_1(A_2983)) | ~m1_subset_1(B_2984, k1_zfmisc_1(A_2983)))), inference(resolution, [status(thm)], [c_67824, c_20])).
% 44.71/33.77  tff(c_116431, plain, (![A_4138, B_4139, C_4140, A_4141]: (m1_subset_1('#skF_1'(A_4138, B_4139, C_4140), C_4140) | m1_subset_1('#skF_1'(A_4138, B_4139, C_4140), A_4141) | ~m1_subset_1(B_4139, k1_zfmisc_1(A_4141)) | C_4140=B_4139 | ~m1_subset_1(C_4140, k1_zfmisc_1(A_4138)) | ~m1_subset_1(B_4139, k1_zfmisc_1(A_4138)))), inference(resolution, [status(thm)], [c_74176, c_20])).
% 44.71/33.77  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_22, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 44.71/33.77  tff(c_58785, plain, (![C_2124, A_2125, B_2126]: (r2_hidden(C_2124, A_2125) | ~r2_hidden(C_2124, B_2126) | ~m1_subset_1(B_2126, k1_zfmisc_1(A_2125)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 44.71/33.77  tff(c_58822, plain, (![A_2132, A_2133, B_2134]: (r2_hidden(A_2132, A_2133) | ~m1_subset_1(B_2134, k1_zfmisc_1(A_2133)) | v1_xboole_0(B_2134) | ~m1_subset_1(A_2132, B_2134))), inference(resolution, [status(thm)], [c_22, c_58785])).
% 44.71/33.77  tff(c_58829, plain, (![A_2132]: (r2_hidden(A_2132, u1_struct_0('#skF_7')) | v1_xboole_0('#skF_8') | ~m1_subset_1(A_2132, '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_58822])).
% 44.71/33.77  tff(c_58834, plain, (![A_2132]: (r2_hidden(A_2132, u1_struct_0('#skF_7')) | ~m1_subset_1(A_2132, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_58829])).
% 44.71/33.77  tff(c_80, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_58835, plain, (![A_2135]: (r2_hidden(A_2135, u1_struct_0('#skF_7')) | ~m1_subset_1(A_2135, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_58829])).
% 44.71/33.77  tff(c_58845, plain, (![A_2135]: (m1_subset_1(A_2135, u1_struct_0('#skF_7')) | ~m1_subset_1(A_2135, '#skF_8'))), inference(resolution, [status(thm)], [c_58835, c_20])).
% 44.71/33.77  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.71/33.77  tff(c_58968, plain, (![A_2159, B_2160, C_2161]: (r2_hidden('#skF_3'(A_2159, B_2160, C_2161), B_2160) | r2_lattice3(A_2159, B_2160, C_2161) | ~m1_subset_1(C_2161, u1_struct_0(A_2159)) | ~l1_orders_2(A_2159))), inference(cnfTransformation, [status(thm)], [f_89])).
% 44.71/33.77  tff(c_26, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 44.71/33.77  tff(c_59007, plain, (![B_2167, A_2168, C_2169]: (~r1_tarski(B_2167, '#skF_3'(A_2168, B_2167, C_2169)) | r2_lattice3(A_2168, B_2167, C_2169) | ~m1_subset_1(C_2169, u1_struct_0(A_2168)) | ~l1_orders_2(A_2168))), inference(resolution, [status(thm)], [c_58968, c_26])).
% 44.71/33.77  tff(c_59028, plain, (![A_2171, C_2172]: (r2_lattice3(A_2171, k1_xboole_0, C_2172) | ~m1_subset_1(C_2172, u1_struct_0(A_2171)) | ~l1_orders_2(A_2171))), inference(resolution, [status(thm)], [c_2, c_59007])).
% 44.71/33.77  tff(c_59048, plain, (![A_2135]: (r2_lattice3('#skF_7', k1_xboole_0, A_2135) | ~l1_orders_2('#skF_7') | ~m1_subset_1(A_2135, '#skF_8'))), inference(resolution, [status(thm)], [c_58845, c_59028])).
% 44.71/33.77  tff(c_59072, plain, (![A_2135]: (r2_lattice3('#skF_7', k1_xboole_0, A_2135) | ~m1_subset_1(A_2135, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_59048])).
% 44.71/33.77  tff(c_74, plain, (v13_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_122, plain, (![A_93, B_94]: (r2_hidden(A_93, B_94) | v1_xboole_0(B_94) | ~m1_subset_1(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_64])).
% 44.71/33.77  tff(c_98, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_115, plain, (~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_98])).
% 44.71/33.77  tff(c_125, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_122, c_115])).
% 44.71/33.77  tff(c_134, plain, (~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_125])).
% 44.71/33.77  tff(c_92, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_137, plain, (~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_115, c_92])).
% 44.71/33.77  tff(c_145, plain, (![B_98, A_99]: (v1_subset_1(B_98, A_99) | B_98=A_99 | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_158])).
% 44.71/33.77  tff(c_151, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_72, c_145])).
% 44.71/33.77  tff(c_157, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_137, c_151])).
% 44.71/33.77  tff(c_105, plain, (![A_89]: (k1_yellow_0(A_89, k1_xboole_0)=k3_yellow_0(A_89) | ~l1_orders_2(A_89))), inference(cnfTransformation, [status(thm)], [f_93])).
% 44.71/33.77  tff(c_109, plain, (k1_yellow_0('#skF_7', k1_xboole_0)=k3_yellow_0('#skF_7')), inference(resolution, [status(thm)], [c_80, c_105])).
% 44.71/33.77  tff(c_116, plain, (![A_91, B_92]: (m1_subset_1(k1_yellow_0(A_91, B_92), u1_struct_0(A_91)) | ~l1_orders_2(A_91))), inference(cnfTransformation, [status(thm)], [f_115])).
% 44.71/33.77  tff(c_119, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_109, c_116])).
% 44.71/33.77  tff(c_121, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_119])).
% 44.71/33.77  tff(c_171, plain, (m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_121])).
% 44.71/33.77  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_171])).
% 44.71/33.77  tff(c_176, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_98])).
% 44.71/33.77  tff(c_187, plain, (![A_102, B_103]: (m1_subset_1(k1_yellow_0(A_102, B_103), u1_struct_0(A_102)) | ~l1_orders_2(A_102))), inference(cnfTransformation, [status(thm)], [f_115])).
% 44.71/33.77  tff(c_190, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_109, c_187])).
% 44.71/33.77  tff(c_192, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_190])).
% 44.71/33.77  tff(c_90, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_84, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_82, plain, (v1_yellow_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 44.71/33.77  tff(c_54, plain, (![A_52]: (r1_yellow_0(A_52, k1_xboole_0) | ~l1_orders_2(A_52) | ~v1_yellow_0(A_52) | ~v5_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.71/33.77  tff(c_60639, plain, (![A_2344, B_2345, D_2346]: (r1_orders_2(A_2344, k1_yellow_0(A_2344, B_2345), D_2346) | ~r2_lattice3(A_2344, B_2345, D_2346) | ~m1_subset_1(D_2346, u1_struct_0(A_2344)) | ~r1_yellow_0(A_2344, B_2345) | ~m1_subset_1(k1_yellow_0(A_2344, B_2345), u1_struct_0(A_2344)) | ~l1_orders_2(A_2344))), inference(cnfTransformation, [status(thm)], [f_111])).
% 44.71/33.77  tff(c_60649, plain, (![D_2346]: (r1_orders_2('#skF_7', k1_yellow_0('#skF_7', k1_xboole_0), D_2346) | ~r2_lattice3('#skF_7', k1_xboole_0, D_2346) | ~m1_subset_1(D_2346, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_60639])).
% 44.71/33.77  tff(c_60658, plain, (![D_2346]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), D_2346) | ~r2_lattice3('#skF_7', k1_xboole_0, D_2346) | ~m1_subset_1(D_2346, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_192, c_109, c_60649])).
% 44.71/33.77  tff(c_60659, plain, (~r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_60658])).
% 44.71/33.77  tff(c_60662, plain, (~l1_orders_2('#skF_7') | ~v1_yellow_0('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_54, c_60659])).
% 44.71/33.77  tff(c_60665, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_60662])).
% 44.71/33.77  tff(c_60667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_60665])).
% 44.71/33.77  tff(c_60668, plain, (![D_2346]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), D_2346) | ~r2_lattice3('#skF_7', k1_xboole_0, D_2346) | ~m1_subset_1(D_2346, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_60658])).
% 44.71/33.77  tff(c_60712, plain, (![D_2359, B_2360, A_2361, C_2362]: (r2_hidden(D_2359, B_2360) | ~r1_orders_2(A_2361, C_2362, D_2359) | ~r2_hidden(C_2362, B_2360) | ~m1_subset_1(D_2359, u1_struct_0(A_2361)) | ~m1_subset_1(C_2362, u1_struct_0(A_2361)) | ~v13_waybel_0(B_2360, A_2361) | ~m1_subset_1(B_2360, k1_zfmisc_1(u1_struct_0(A_2361))) | ~l1_orders_2(A_2361))), inference(cnfTransformation, [status(thm)], [f_151])).
% 44.71/33.77  tff(c_60716, plain, (![D_2346, B_2360]: (r2_hidden(D_2346, B_2360) | ~r2_hidden(k3_yellow_0('#skF_7'), B_2360) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_2360, '#skF_7') | ~m1_subset_1(B_2360, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_2346) | ~m1_subset_1(D_2346, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_60668, c_60712])).
% 44.71/33.77  tff(c_68603, plain, (![D_2708, B_2709]: (r2_hidden(D_2708, B_2709) | ~r2_hidden(k3_yellow_0('#skF_7'), B_2709) | ~v13_waybel_0(B_2709, '#skF_7') | ~m1_subset_1(B_2709, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_2708) | ~m1_subset_1(D_2708, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_192, c_60716])).
% 44.71/33.77  tff(c_68656, plain, (![D_2708]: (r2_hidden(D_2708, '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_2708) | ~m1_subset_1(D_2708, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_72, c_68603])).
% 44.71/33.77  tff(c_68679, plain, (![D_2710]: (r2_hidden(D_2710, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_2710) | ~m1_subset_1(D_2710, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_176, c_68656])).
% 44.71/33.77  tff(c_68831, plain, (![A_2711]: (r2_hidden(A_2711, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, A_2711) | ~m1_subset_1(A_2711, '#skF_8'))), inference(resolution, [status(thm)], [c_58845, c_68679])).
% 44.71/33.77  tff(c_68942, plain, (![A_2712]: (r2_hidden(A_2712, '#skF_8') | ~m1_subset_1(A_2712, '#skF_8'))), inference(resolution, [status(thm)], [c_59072, c_68831])).
% 44.71/33.77  tff(c_8, plain, (![A_6, B_7, C_11]: (~r2_hidden('#skF_1'(A_6, B_7, C_11), C_11) | ~r2_hidden('#skF_1'(A_6, B_7, C_11), B_7) | C_11=B_7 | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 44.71/33.77  tff(c_72166, plain, (![A_2911, B_2912]: (~r2_hidden('#skF_1'(A_2911, B_2912, '#skF_8'), B_2912) | B_2912='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_2911)) | ~m1_subset_1(B_2912, k1_zfmisc_1(A_2911)) | ~m1_subset_1('#skF_1'(A_2911, B_2912, '#skF_8'), '#skF_8'))), inference(resolution, [status(thm)], [c_68942, c_8])).
% 44.71/33.77  tff(c_72256, plain, (![A_2911]: (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_2911)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2911)) | ~m1_subset_1('#skF_1'(A_2911, u1_struct_0('#skF_7'), '#skF_8'), '#skF_8'))), inference(resolution, [status(thm)], [c_58834, c_72166])).
% 44.71/33.77  tff(c_72258, plain, (![A_2911]: (~m1_subset_1('#skF_8', k1_zfmisc_1(A_2911)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2911)) | ~m1_subset_1('#skF_1'(A_2911, u1_struct_0('#skF_7'), '#skF_8'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_72256])).
% 44.71/33.77  tff(c_117196, plain, (![A_4138, A_4141]: (m1_subset_1('#skF_1'(A_4138, u1_struct_0('#skF_7'), '#skF_8'), A_4141) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4141)) | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_4138)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4138)))), inference(resolution, [status(thm)], [c_116431, c_72258])).
% 44.71/33.77  tff(c_117365, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(splitLeft, [status(thm)], [c_117196])).
% 44.71/33.77  tff(c_58777, plain, (![A_2120, C_2121, B_2122]: (m1_subset_1(A_2120, C_2121) | ~m1_subset_1(B_2122, k1_zfmisc_1(C_2121)) | ~r2_hidden(A_2120, B_2122))), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.71/33.77  tff(c_58783, plain, (![A_2120]: (m1_subset_1(A_2120, u1_struct_0('#skF_7')) | ~r2_hidden(A_2120, '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_58777])).
% 44.71/33.77  tff(c_59659, plain, (![A_2261, B_2262, C_2263, A_2]: (r2_hidden('#skF_1'(A_2261, B_2262, C_2263), A_2) | ~m1_subset_1(C_2263, k1_zfmisc_1(A_2)) | r2_hidden('#skF_1'(A_2261, B_2262, C_2263), B_2262) | C_2263=B_2262 | ~m1_subset_1(C_2263, k1_zfmisc_1(A_2261)) | ~m1_subset_1(B_2262, k1_zfmisc_1(A_2261)))), inference(resolution, [status(thm)], [c_59611, c_4])).
% 44.71/33.77  tff(c_67655, plain, (![C_2661, A_2662, A_2663]: (~m1_subset_1(C_2661, k1_zfmisc_1(A_2662)) | C_2661=A_2662 | ~m1_subset_1(C_2661, k1_zfmisc_1(A_2663)) | ~m1_subset_1(A_2662, k1_zfmisc_1(A_2663)) | r2_hidden('#skF_1'(A_2663, A_2662, C_2661), A_2662))), inference(factorization, [status(thm), theory('equality')], [c_59659])).
% 44.71/33.77  tff(c_59462, plain, (![A_2241, B_2242, C_2243]: (~r2_hidden('#skF_1'(A_2241, B_2242, C_2243), C_2243) | ~r2_hidden('#skF_1'(A_2241, B_2242, C_2243), B_2242) | C_2243=B_2242 | ~m1_subset_1(C_2243, k1_zfmisc_1(A_2241)) | ~m1_subset_1(B_2242, k1_zfmisc_1(A_2241)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 44.71/33.77  tff(c_59470, plain, (![A_2241, B_2242, B_18]: (~r2_hidden('#skF_1'(A_2241, B_2242, B_18), B_2242) | B_2242=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_2241)) | ~m1_subset_1(B_2242, k1_zfmisc_1(A_2241)) | v1_xboole_0(B_18) | ~m1_subset_1('#skF_1'(A_2241, B_2242, B_18), B_18))), inference(resolution, [status(thm)], [c_22, c_59462])).
% 44.71/33.77  tff(c_68297, plain, (![C_2693, A_2694, A_2695]: (v1_xboole_0(C_2693) | ~m1_subset_1('#skF_1'(A_2694, A_2695, C_2693), C_2693) | ~m1_subset_1(C_2693, k1_zfmisc_1(A_2695)) | C_2693=A_2695 | ~m1_subset_1(C_2693, k1_zfmisc_1(A_2694)) | ~m1_subset_1(A_2695, k1_zfmisc_1(A_2694)))), inference(resolution, [status(thm)], [c_67655, c_59470])).
% 44.71/33.77  tff(c_68363, plain, (![A_2695, A_2694]: (v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2695)) | u1_struct_0('#skF_7')=A_2695 | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2694)) | ~m1_subset_1(A_2695, k1_zfmisc_1(A_2694)) | ~r2_hidden('#skF_1'(A_2694, A_2695, u1_struct_0('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_58783, c_68297])).
% 44.71/33.77  tff(c_68602, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_68363])).
% 44.71/33.77  tff(c_117553, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_117365, c_68602])).
% 44.71/33.77  tff(c_117596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_117553])).
% 44.71/33.77  tff(c_117598, plain, (u1_struct_0('#skF_7')!='#skF_8'), inference(splitRight, [status(thm)], [c_117196])).
% 44.71/33.77  tff(c_6, plain, (![A_6, B_7, C_11]: (m1_subset_1('#skF_1'(A_6, B_7, C_11), A_6) | C_11=B_7 | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 44.71/33.77  tff(c_59067, plain, (![A_2171, B_7, C_11]: (r2_lattice3(A_2171, k1_xboole_0, '#skF_1'(u1_struct_0(A_2171), B_7, C_11)) | ~l1_orders_2(A_2171) | C_11=B_7 | ~m1_subset_1(C_11, k1_zfmisc_1(u1_struct_0(A_2171))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_2171))))), inference(resolution, [status(thm)], [c_6, c_59028])).
% 44.71/33.77  tff(c_118036, plain, (![A_4146, A_4147]: (m1_subset_1('#skF_1'(A_4146, u1_struct_0('#skF_7'), '#skF_8'), A_4147) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4147)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_4146)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4146)))), inference(splitRight, [status(thm)], [c_117196])).
% 44.71/33.77  tff(c_68678, plain, (![D_2708]: (r2_hidden(D_2708, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_2708) | ~m1_subset_1(D_2708, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_176, c_68656])).
% 44.71/33.77  tff(c_118294, plain, (![A_4146]: (r2_hidden('#skF_1'(A_4146, u1_struct_0('#skF_7'), '#skF_8'), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(A_4146, u1_struct_0('#skF_7'), '#skF_8')) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_4146)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4146)))), inference(resolution, [status(thm)], [c_118036, c_68678])).
% 44.71/33.77  tff(c_118553, plain, (![A_4148]: (r2_hidden('#skF_1'(A_4148, u1_struct_0('#skF_7'), '#skF_8'), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(A_4148, u1_struct_0('#skF_7'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_4148)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_4148)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_118294])).
% 44.71/33.77  tff(c_118589, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), '#skF_8'), '#skF_8') | ~l1_orders_2('#skF_7') | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_59067, c_118553])).
% 44.71/33.77  tff(c_118628, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), '#skF_8'), '#skF_8') | u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_72, c_80, c_118589])).
% 44.71/33.77  tff(c_118629, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_117598, c_118628])).
% 44.71/33.77  tff(c_118657, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_118629, c_20])).
% 44.71/33.77  tff(c_67375, plain, (![A_2653, B_2654, C_2655, A_2656]: (r2_hidden('#skF_1'(A_2653, B_2654, C_2655), A_2656) | ~m1_subset_1(C_2655, k1_zfmisc_1(A_2656)) | r2_hidden('#skF_1'(A_2653, B_2654, C_2655), B_2654) | C_2655=B_2654 | ~m1_subset_1(C_2655, k1_zfmisc_1(A_2653)) | ~m1_subset_1(B_2654, k1_zfmisc_1(A_2653)))), inference(resolution, [status(thm)], [c_59611, c_4])).
% 44.71/33.77  tff(c_80100, plain, (![B_3189, A_3190, A_3188, A_3187, C_3191]: (r2_hidden('#skF_1'(A_3188, B_3189, C_3191), A_3190) | ~m1_subset_1(A_3187, k1_zfmisc_1(A_3190)) | ~m1_subset_1(C_3191, k1_zfmisc_1(A_3187)) | r2_hidden('#skF_1'(A_3188, B_3189, C_3191), B_3189) | C_3191=B_3189 | ~m1_subset_1(C_3191, k1_zfmisc_1(A_3188)) | ~m1_subset_1(B_3189, k1_zfmisc_1(A_3188)))), inference(resolution, [status(thm)], [c_67375, c_4])).
% 44.71/33.77  tff(c_80222, plain, (![A_3188, B_3189, C_3191]: (r2_hidden('#skF_1'(A_3188, B_3189, C_3191), u1_struct_0('#skF_7')) | ~m1_subset_1(C_3191, k1_zfmisc_1('#skF_8')) | r2_hidden('#skF_1'(A_3188, B_3189, C_3191), B_3189) | C_3191=B_3189 | ~m1_subset_1(C_3191, k1_zfmisc_1(A_3188)) | ~m1_subset_1(B_3189, k1_zfmisc_1(A_3188)))), inference(resolution, [status(thm)], [c_72, c_80100])).
% 44.71/33.77  tff(c_81970, plain, (![C_3227, A_3228]: (~m1_subset_1(C_3227, k1_zfmisc_1('#skF_8')) | u1_struct_0('#skF_7')=C_3227 | ~m1_subset_1(C_3227, k1_zfmisc_1(A_3228)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_3228)) | r2_hidden('#skF_1'(A_3228, u1_struct_0('#skF_7'), C_3227), u1_struct_0('#skF_7')))), inference(factorization, [status(thm), theory('equality')], [c_80222])).
% 44.71/33.77  tff(c_82012, plain, (![C_3227, A_3228]: (v1_xboole_0(C_3227) | ~m1_subset_1('#skF_1'(A_3228, u1_struct_0('#skF_7'), C_3227), C_3227) | ~m1_subset_1(C_3227, k1_zfmisc_1('#skF_8')) | u1_struct_0('#skF_7')=C_3227 | ~m1_subset_1(C_3227, k1_zfmisc_1(A_3228)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_3228)))), inference(resolution, [status(thm)], [c_81970, c_59470])).
% 44.71/33.77  tff(c_118661, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_118657, c_82012])).
% 44.71/33.77  tff(c_118687, plain, (v1_xboole_0('#skF_8') | u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_72, c_58757, c_118661])).
% 44.71/33.77  tff(c_118689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117598, c_78, c_118687])).
% 44.71/33.77  tff(c_118690, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_72256])).
% 44.71/33.77  tff(c_118722, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_118690, c_68602])).
% 44.71/33.77  tff(c_118774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_118722])).
% 44.71/33.77  tff(c_118776, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_68363])).
% 44.71/33.77  tff(c_60292, plain, (![A_2320, B_2321, C_2322]: (m1_subset_1('#skF_1'(A_2320, B_2321, C_2322), B_2321) | r2_hidden('#skF_1'(A_2320, B_2321, C_2322), C_2322) | C_2322=B_2321 | ~m1_subset_1(C_2322, k1_zfmisc_1(A_2320)) | ~m1_subset_1(B_2321, k1_zfmisc_1(A_2320)))), inference(resolution, [status(thm)], [c_59611, c_20])).
% 44.71/33.77  tff(c_60390, plain, (![A_2320, B_2321, C_2322]: (m1_subset_1('#skF_1'(A_2320, B_2321, C_2322), C_2322) | m1_subset_1('#skF_1'(A_2320, B_2321, C_2322), B_2321) | C_2322=B_2321 | ~m1_subset_1(C_2322, k1_zfmisc_1(A_2320)) | ~m1_subset_1(B_2321, k1_zfmisc_1(A_2320)))), inference(resolution, [status(thm)], [c_60292, c_20])).
% 44.71/33.77  tff(c_118806, plain, (![D_4152, B_4153]: (r2_hidden(D_4152, B_4153) | ~r2_hidden(k3_yellow_0('#skF_7'), B_4153) | ~v13_waybel_0(B_4153, '#skF_7') | ~m1_subset_1(B_4153, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_4152) | ~m1_subset_1(D_4152, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_192, c_60716])).
% 44.71/33.77  tff(c_118859, plain, (![D_4152]: (r2_hidden(D_4152, '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_4152) | ~m1_subset_1(D_4152, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_72, c_118806])).
% 44.71/33.77  tff(c_118882, plain, (![D_4154]: (r2_hidden(D_4154, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_4154) | ~m1_subset_1(D_4154, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_176, c_118859])).
% 44.71/33.77  tff(c_119067, plain, (![A_4157]: (r2_hidden(A_4157, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, A_4157) | ~m1_subset_1(A_4157, '#skF_8'))), inference(resolution, [status(thm)], [c_58845, c_118882])).
% 44.71/33.77  tff(c_119170, plain, (![A_2135]: (r2_hidden(A_2135, '#skF_8') | ~m1_subset_1(A_2135, '#skF_8'))), inference(resolution, [status(thm)], [c_59072, c_119067])).
% 44.71/33.77  tff(c_67931, plain, (![A_2672, B_2673, C_2674, A_2675]: (m1_subset_1('#skF_1'(A_2672, B_2673, C_2674), A_2675) | ~m1_subset_1(B_2673, k1_zfmisc_1(A_2675)) | r2_hidden('#skF_1'(A_2672, B_2673, C_2674), C_2674) | C_2674=B_2673 | ~m1_subset_1(C_2674, k1_zfmisc_1(A_2672)) | ~m1_subset_1(B_2673, k1_zfmisc_1(A_2672)))), inference(resolution, [status(thm)], [c_67824, c_20])).
% 44.71/33.77  tff(c_61561, plain, (![A_2404, B_2405, B_2406]: (~r2_hidden('#skF_1'(A_2404, B_2405, B_2406), B_2405) | B_2406=B_2405 | ~m1_subset_1(B_2406, k1_zfmisc_1(A_2404)) | ~m1_subset_1(B_2405, k1_zfmisc_1(A_2404)) | v1_xboole_0(B_2406) | ~m1_subset_1('#skF_1'(A_2404, B_2405, B_2406), B_2406))), inference(resolution, [status(thm)], [c_22, c_59462])).
% 44.71/33.77  tff(c_121099, plain, (![B_4287, B_4286, A_4288]: (B_4287=B_4286 | ~m1_subset_1(B_4286, k1_zfmisc_1(A_4288)) | ~m1_subset_1(B_4287, k1_zfmisc_1(A_4288)) | v1_xboole_0(B_4286) | ~m1_subset_1('#skF_1'(A_4288, B_4287, B_4286), B_4286) | v1_xboole_0(B_4287) | ~m1_subset_1('#skF_1'(A_4288, B_4287, B_4286), B_4287))), inference(resolution, [status(thm)], [c_22, c_61561])).
% 44.71/33.77  tff(c_121124, plain, (![A_6, B_7]: (v1_xboole_0(A_6) | v1_xboole_0(B_7) | ~m1_subset_1('#skF_1'(A_6, B_7, A_6), B_7) | B_7=A_6 | ~m1_subset_1(A_6, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_6, c_121099])).
% 44.71/33.77  tff(c_121589, plain, (![A_4301, B_4302]: (v1_xboole_0(A_4301) | v1_xboole_0(B_4302) | ~m1_subset_1('#skF_1'(A_4301, B_4302, A_4301), B_4302) | B_4302=A_4301 | ~m1_subset_1(B_4302, k1_zfmisc_1(A_4301)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_121124])).
% 44.71/33.77  tff(c_121593, plain, (![C_2674, A_2675]: (v1_xboole_0(C_2674) | v1_xboole_0(A_2675) | ~m1_subset_1(A_2675, k1_zfmisc_1(A_2675)) | r2_hidden('#skF_1'(C_2674, A_2675, C_2674), C_2674) | C_2674=A_2675 | ~m1_subset_1(C_2674, k1_zfmisc_1(C_2674)) | ~m1_subset_1(A_2675, k1_zfmisc_1(C_2674)))), inference(resolution, [status(thm)], [c_67931, c_121589])).
% 44.71/33.77  tff(c_121680, plain, (![C_4303, A_4304]: (v1_xboole_0(C_4303) | v1_xboole_0(A_4304) | r2_hidden('#skF_1'(C_4303, A_4304, C_4303), C_4303) | C_4303=A_4304 | ~m1_subset_1(A_4304, k1_zfmisc_1(C_4303)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_58757, c_121593])).
% 44.71/33.77  tff(c_121723, plain, (![C_4303, A_4304]: (~r2_hidden('#skF_1'(C_4303, A_4304, C_4303), A_4304) | ~m1_subset_1(C_4303, k1_zfmisc_1(C_4303)) | v1_xboole_0(C_4303) | v1_xboole_0(A_4304) | C_4303=A_4304 | ~m1_subset_1(A_4304, k1_zfmisc_1(C_4303)))), inference(resolution, [status(thm)], [c_121680, c_8])).
% 44.71/33.77  tff(c_122023, plain, (![C_4314, A_4315]: (~r2_hidden('#skF_1'(C_4314, A_4315, C_4314), A_4315) | v1_xboole_0(C_4314) | v1_xboole_0(A_4315) | C_4314=A_4315 | ~m1_subset_1(A_4315, k1_zfmisc_1(C_4314)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_121723])).
% 44.71/33.77  tff(c_122039, plain, (![C_4314]: (v1_xboole_0(C_4314) | v1_xboole_0('#skF_8') | C_4314='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(C_4314)) | ~m1_subset_1('#skF_1'(C_4314, '#skF_8', C_4314), '#skF_8'))), inference(resolution, [status(thm)], [c_119170, c_122023])).
% 44.71/33.77  tff(c_122164, plain, (![C_4316]: (v1_xboole_0(C_4316) | C_4316='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(C_4316)) | ~m1_subset_1('#skF_1'(C_4316, '#skF_8', C_4316), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_122039])).
% 44.71/33.77  tff(c_122184, plain, (![C_2322]: (v1_xboole_0(C_2322) | m1_subset_1('#skF_1'(C_2322, '#skF_8', C_2322), C_2322) | C_2322='#skF_8' | ~m1_subset_1(C_2322, k1_zfmisc_1(C_2322)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(C_2322)))), inference(resolution, [status(thm)], [c_60390, c_122164])).
% 44.71/33.77  tff(c_122483, plain, (![C_4321]: (v1_xboole_0(C_4321) | m1_subset_1('#skF_1'(C_4321, '#skF_8', C_4321), C_4321) | C_4321='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(C_4321)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_122184])).
% 44.71/33.77  tff(c_118881, plain, (![D_4152]: (r2_hidden(D_4152, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_4152) | ~m1_subset_1(D_4152, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_176, c_118859])).
% 44.71/33.77  tff(c_122533, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7'))) | v1_xboole_0(u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_122483, c_118881])).
% 44.71/33.77  tff(c_122650, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7'))) | v1_xboole_0(u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_122533])).
% 44.71/33.77  tff(c_122651, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7'))) | u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_118776, c_122650])).
% 44.71/33.77  tff(c_123214, plain, (~r2_lattice3('#skF_7', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_122651])).
% 44.71/33.77  tff(c_123217, plain, (~l1_orders_2('#skF_7') | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_59067, c_123214])).
% 44.71/33.77  tff(c_123226, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_58757, c_80, c_123217])).
% 44.71/33.77  tff(c_61989, plain, (![B_2428, A_2429]: (u1_struct_0('#skF_7')=B_2428 | ~m1_subset_1(B_2428, k1_zfmisc_1(A_2429)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2429)) | v1_xboole_0(B_2428) | ~m1_subset_1('#skF_1'(A_2429, u1_struct_0('#skF_7'), B_2428), B_2428) | ~m1_subset_1('#skF_1'(A_2429, u1_struct_0('#skF_7'), B_2428), '#skF_8'))), inference(resolution, [status(thm)], [c_58834, c_61561])).
% 44.71/33.77  tff(c_62003, plain, (![A_6]: (v1_xboole_0(A_6) | ~m1_subset_1('#skF_1'(A_6, u1_struct_0('#skF_7'), A_6), '#skF_8') | u1_struct_0('#skF_7')=A_6 | ~m1_subset_1(A_6, k1_zfmisc_1(A_6)) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_6, c_61989])).
% 44.71/33.77  tff(c_67340, plain, (![A_2652]: (v1_xboole_0(A_2652) | ~m1_subset_1('#skF_1'(A_2652, u1_struct_0('#skF_7'), A_2652), '#skF_8') | u1_struct_0('#skF_7')=A_2652 | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_2652)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_62003])).
% 44.71/33.77  tff(c_67352, plain, (v1_xboole_0('#skF_8') | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_67340])).
% 44.71/33.77  tff(c_67358, plain, (v1_xboole_0('#skF_8') | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_67352])).
% 44.71/33.77  tff(c_67359, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_67358])).
% 44.71/33.77  tff(c_67360, plain, (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_67359])).
% 44.71/33.77  tff(c_123543, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_123226, c_67360])).
% 44.71/33.77  tff(c_123592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58757, c_123543])).
% 44.71/33.77  tff(c_123593, plain, (u1_struct_0('#skF_7')='#skF_8' | r2_hidden('#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')), '#skF_8')), inference(splitRight, [status(thm)], [c_122651])).
% 44.71/33.77  tff(c_123620, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_7'), '#skF_8', u1_struct_0('#skF_7')), '#skF_8')), inference(splitLeft, [status(thm)], [c_123593])).
% 44.71/33.77  tff(c_121766, plain, (![C_4303, A_4304]: (~r2_hidden('#skF_1'(C_4303, A_4304, C_4303), A_4304) | v1_xboole_0(C_4303) | v1_xboole_0(A_4304) | C_4303=A_4304 | ~m1_subset_1(A_4304, k1_zfmisc_1(C_4303)))), inference(demodulation, [status(thm), theory('equality')], [c_58757, c_121723])).
% 44.71/33.77  tff(c_123655, plain, (v1_xboole_0(u1_struct_0('#skF_7')) | v1_xboole_0('#skF_8') | u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_123620, c_121766])).
% 44.71/33.77  tff(c_123676, plain, (v1_xboole_0(u1_struct_0('#skF_7')) | v1_xboole_0('#skF_8') | u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_123655])).
% 44.71/33.77  tff(c_123677, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_78, c_118776, c_123676])).
% 44.71/33.77  tff(c_123732, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_123677, c_67360])).
% 44.71/33.77  tff(c_123781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58757, c_123732])).
% 44.71/33.77  tff(c_123782, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_123593])).
% 44.71/33.77  tff(c_123822, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_123782, c_67360])).
% 44.71/33.77  tff(c_123871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58757, c_123822])).
% 44.71/33.77  tff(c_123872, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_67359])).
% 44.71/33.77  tff(c_175, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_98])).
% 44.71/33.77  tff(c_123919, plain, (v1_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_123872, c_175])).
% 44.71/33.77  tff(c_123925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58758, c_123919])).
% 44.71/33.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.71/33.77  
% 44.71/33.77  Inference rules
% 44.71/33.77  ----------------------
% 44.71/33.77  #Ref     : 0
% 44.71/33.77  #Sup     : 25481
% 44.71/33.77  #Fact    : 54
% 44.71/33.77  #Define  : 0
% 44.71/33.77  #Split   : 95
% 44.71/33.77  #Chain   : 0
% 44.71/33.77  #Close   : 0
% 44.71/33.77  
% 44.71/33.77  Ordering : KBO
% 44.71/33.77  
% 44.71/33.77  Simplification rules
% 44.71/33.77  ----------------------
% 44.71/33.77  #Subsume      : 7683
% 44.71/33.77  #Demod        : 11346
% 44.71/33.77  #Tautology    : 1837
% 44.71/33.77  #SimpNegUnit  : 1144
% 44.71/33.77  #BackRed      : 1593
% 44.71/33.77  
% 44.71/33.77  #Partial instantiations: 0
% 44.71/33.78  #Strategies tried      : 1
% 44.71/33.78  
% 44.71/33.78  Timing (in seconds)
% 44.71/33.78  ----------------------
% 44.71/33.78  Preprocessing        : 0.38
% 44.71/33.78  Parsing              : 0.20
% 44.71/33.78  CNF conversion       : 0.03
% 44.71/33.78  Main loop            : 32.58
% 44.71/33.78  Inferencing          : 4.64
% 44.71/33.78  Reduction            : 7.08
% 44.71/33.78  Demodulation         : 5.09
% 44.71/33.78  BG Simplification    : 0.47
% 44.71/33.78  Subsumption          : 18.68
% 44.71/33.78  Abstraction          : 0.82
% 44.71/33.78  MUC search           : 0.00
% 44.71/33.78  Cooper               : 0.00
% 44.71/33.78  Total                : 33.04
% 44.71/33.78  Index Insertion      : 0.00
% 44.71/33.78  Index Deletion       : 0.00
% 44.71/33.78  Index Matching       : 0.00
% 44.71/33.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
