%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 145 expanded)
%              Number of leaves         :   47 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 247 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_48,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_48,plain,(
    ! [A_32] : l1_orders_2(k2_yellow_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [A_49,B_50] : k2_xboole_0(k1_tarski(A_49),B_50) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [A_49] : k1_tarski(A_49) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_106])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_268,plain,(
    ! [A_89,B_90] :
      ( k6_domain_1(A_89,B_90) = k1_tarski(B_90)
      | ~ m1_subset_1(B_90,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_274,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_268])).

tff(c_278,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_274])).

tff(c_422,plain,(
    ! [A_110,B_111] :
      ( m1_subset_1(k6_domain_1(A_110,B_111),k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_431,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_422])).

tff(c_435,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_431])).

tff(c_436,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_435])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_459,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_32])).

tff(c_54,plain,(
    ! [B_36,A_34] :
      ( B_36 = A_34
      | ~ r1_tarski(A_34,B_36)
      | ~ v1_zfmisc_1(B_36)
      | v1_xboole_0(B_36)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_462,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_459,c_54])).

tff(c_473,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_462])).

tff(c_474,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_473])).

tff(c_478,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_204,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_163])).

tff(c_222,plain,(
    ! [A_75] :
      ( k1_xboole_0 = A_75
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_215,c_172])).

tff(c_483,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_478,c_222])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_483])).

tff(c_489,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_58,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_417,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_58])).

tff(c_493,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_417])).

tff(c_50,plain,(
    ! [A_33] : u1_struct_0(k2_yellow_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_117,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_125,plain,(
    ! [A_32] : u1_struct_0(k2_yellow_1(A_32)) = k2_struct_0(k2_yellow_1(A_32)) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_127,plain,(
    ! [A_32] : k2_struct_0(k2_yellow_1(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_152,plain,(
    ! [A_62] :
      ( ~ v1_subset_1(k2_struct_0(A_62),u1_struct_0(A_62))
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [A_33] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_33)),A_33)
      | ~ l1_struct_0(k2_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_152])).

tff(c_160,plain,(
    ! [A_33] :
      ( ~ v1_subset_1(A_33,A_33)
      | ~ l1_struct_0(k2_yellow_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_158])).

tff(c_506,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_493,c_160])).

tff(c_510,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_506])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.32  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.39/1.32  
% 2.39/1.32  %Foreground sorts:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Background operators:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Foreground operators:
% 2.39/1.32  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.39/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.32  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.39/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.39/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.39/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.32  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.39/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.39/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.39/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.32  
% 2.39/1.34  tff(f_94, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.39/1.34  tff(f_83, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.39/1.34  tff(f_48, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.39/1.34  tff(f_59, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.39/1.34  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.39/1.34  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.39/1.34  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.39/1.34  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.34  tff(f_111, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.39/1.34  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.39/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.34  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.39/1.34  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.34  tff(f_98, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.39/1.34  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.39/1.34  tff(f_72, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.39/1.34  tff(c_48, plain, (![A_32]: (l1_orders_2(k2_yellow_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.39/1.34  tff(c_42, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.39/1.34  tff(c_20, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.39/1.34  tff(c_106, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.34  tff(c_110, plain, (![A_49]: (k1_tarski(A_49)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_106])).
% 2.39/1.34  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.39/1.34  tff(c_56, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.39/1.34  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.39/1.34  tff(c_268, plain, (![A_89, B_90]: (k6_domain_1(A_89, B_90)=k1_tarski(B_90) | ~m1_subset_1(B_90, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.34  tff(c_274, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_268])).
% 2.39/1.34  tff(c_278, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_274])).
% 2.39/1.34  tff(c_422, plain, (![A_110, B_111]: (m1_subset_1(k6_domain_1(A_110, B_111), k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.34  tff(c_431, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_278, c_422])).
% 2.39/1.34  tff(c_435, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_431])).
% 2.39/1.34  tff(c_436, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_435])).
% 2.39/1.34  tff(c_32, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.34  tff(c_459, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_436, c_32])).
% 2.39/1.34  tff(c_54, plain, (![B_36, A_34]: (B_36=A_34 | ~r1_tarski(A_34, B_36) | ~v1_zfmisc_1(B_36) | v1_xboole_0(B_36) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.39/1.34  tff(c_462, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_459, c_54])).
% 2.39/1.34  tff(c_473, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_462])).
% 2.39/1.34  tff(c_474, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_473])).
% 2.39/1.34  tff(c_478, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_474])).
% 2.39/1.34  tff(c_204, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.34  tff(c_215, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_204, c_2])).
% 2.39/1.34  tff(c_22, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.39/1.34  tff(c_163, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.34  tff(c_172, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_163])).
% 2.39/1.34  tff(c_222, plain, (![A_75]: (k1_xboole_0=A_75 | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_215, c_172])).
% 2.39/1.34  tff(c_483, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_478, c_222])).
% 2.39/1.34  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_483])).
% 2.39/1.34  tff(c_489, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_474])).
% 2.39/1.34  tff(c_58, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.39/1.34  tff(c_417, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_58])).
% 2.39/1.34  tff(c_493, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_417])).
% 2.39/1.34  tff(c_50, plain, (![A_33]: (u1_struct_0(k2_yellow_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.39/1.34  tff(c_117, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.34  tff(c_122, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_42, c_117])).
% 2.39/1.34  tff(c_125, plain, (![A_32]: (u1_struct_0(k2_yellow_1(A_32))=k2_struct_0(k2_yellow_1(A_32)))), inference(resolution, [status(thm)], [c_48, c_122])).
% 2.39/1.34  tff(c_127, plain, (![A_32]: (k2_struct_0(k2_yellow_1(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_125])).
% 2.39/1.34  tff(c_152, plain, (![A_62]: (~v1_subset_1(k2_struct_0(A_62), u1_struct_0(A_62)) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.39/1.34  tff(c_158, plain, (![A_33]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_33)), A_33) | ~l1_struct_0(k2_yellow_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_152])).
% 2.39/1.34  tff(c_160, plain, (![A_33]: (~v1_subset_1(A_33, A_33) | ~l1_struct_0(k2_yellow_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_158])).
% 2.39/1.34  tff(c_506, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_493, c_160])).
% 2.39/1.34  tff(c_510, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_506])).
% 2.39/1.34  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_510])).
% 2.39/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  Inference rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Ref     : 0
% 2.39/1.34  #Sup     : 94
% 2.39/1.34  #Fact    : 0
% 2.39/1.34  #Define  : 0
% 2.39/1.34  #Split   : 2
% 2.39/1.34  #Chain   : 0
% 2.39/1.34  #Close   : 0
% 2.39/1.34  
% 2.39/1.34  Ordering : KBO
% 2.39/1.34  
% 2.39/1.34  Simplification rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Subsume      : 16
% 2.39/1.34  #Demod        : 28
% 2.39/1.34  #Tautology    : 46
% 2.39/1.34  #SimpNegUnit  : 11
% 2.39/1.34  #BackRed      : 15
% 2.39/1.34  
% 2.39/1.34  #Partial instantiations: 0
% 2.39/1.34  #Strategies tried      : 1
% 2.39/1.34  
% 2.39/1.34  Timing (in seconds)
% 2.39/1.34  ----------------------
% 2.79/1.34  Preprocessing        : 0.32
% 2.79/1.34  Parsing              : 0.17
% 2.79/1.34  CNF conversion       : 0.02
% 2.79/1.34  Main loop            : 0.27
% 2.79/1.34  Inferencing          : 0.10
% 2.79/1.34  Reduction            : 0.08
% 2.79/1.34  Demodulation         : 0.06
% 2.79/1.34  BG Simplification    : 0.02
% 2.79/1.34  Subsumption          : 0.05
% 2.79/1.34  Abstraction          : 0.02
% 2.79/1.34  MUC search           : 0.00
% 2.79/1.34  Cooper               : 0.00
% 2.79/1.34  Total                : 0.62
% 2.79/1.34  Index Insertion      : 0.00
% 2.79/1.34  Index Deletion       : 0.00
% 2.79/1.34  Index Matching       : 0.00
% 2.79/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
