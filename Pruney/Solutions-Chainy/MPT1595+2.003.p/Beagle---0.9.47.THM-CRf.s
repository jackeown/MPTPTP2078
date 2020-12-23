%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 416 expanded)
%              Number of leaves         :   39 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 ( 973 expanded)
%              Number of equality atoms :    9 ( 164 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k2_yellow_1 > k1_yellow_1 > k1_wellord2 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
               => ( r3_orders_2(k2_yellow_1(A),B,C)
                <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_101,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_97,axiom,(
    ! [A] : k1_yellow_1(A) = k1_wellord2(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    ! [A_26] : u1_struct_0(k2_yellow_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_68,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_67,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56])).

tff(c_66,plain,
    ( r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_84,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_22,plain,(
    ! [A_11] : v1_relat_1(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_34,plain,(
    ! [A_22] : l1_orders_2(k2_yellow_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [A_25] : k1_yellow_1(A_25) = k1_wellord2(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [A_26] : u1_orders_2(k2_yellow_1(A_26)) = k1_yellow_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69,plain,(
    ! [A_26] : u1_orders_2(k2_yellow_1(A_26)) = k1_wellord2(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_158,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_orders_2(A_55,B_56,C_57)
      | ~ r2_hidden(k4_tarski(B_56,C_57),u1_orders_2(A_55))
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [A_26,B_56,C_57] :
      ( r1_orders_2(k2_yellow_1(A_26),B_56,C_57)
      | ~ r2_hidden(k4_tarski(B_56,C_57),k1_wellord2(A_26))
      | ~ m1_subset_1(C_57,u1_struct_0(k2_yellow_1(A_26)))
      | ~ m1_subset_1(B_56,u1_struct_0(k2_yellow_1(A_26)))
      | ~ l1_orders_2(k2_yellow_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_158])).

tff(c_168,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_orders_2(k2_yellow_1(A_58),B_59,C_60)
      | ~ r2_hidden(k4_tarski(B_59,C_60),k1_wellord2(A_58))
      | ~ m1_subset_1(C_60,A_58)
      | ~ m1_subset_1(B_59,A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_50,c_164])).

tff(c_175,plain,(
    ! [A_3,C_9,D_10] :
      ( r1_orders_2(k2_yellow_1(A_3),C_9,D_10)
      | ~ m1_subset_1(D_10,A_3)
      | ~ m1_subset_1(C_9,A_3)
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(resolution,[status(thm)],[c_75,c_168])).

tff(c_38,plain,(
    ! [A_23] : v3_orders_2(k2_yellow_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_202,plain,(
    ! [A_73,B_74,C_75] :
      ( r3_orders_2(A_73,B_74,C_75)
      | ~ r1_orders_2(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_204,plain,(
    ! [A_26,B_74,C_75] :
      ( r3_orders_2(k2_yellow_1(A_26),B_74,C_75)
      | ~ r1_orders_2(k2_yellow_1(A_26),B_74,C_75)
      | ~ m1_subset_1(C_75,A_26)
      | ~ m1_subset_1(B_74,u1_struct_0(k2_yellow_1(A_26)))
      | ~ l1_orders_2(k2_yellow_1(A_26))
      | ~ v3_orders_2(k2_yellow_1(A_26))
      | v2_struct_0(k2_yellow_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_202])).

tff(c_207,plain,(
    ! [A_76,B_77,C_78] :
      ( r3_orders_2(k2_yellow_1(A_76),B_77,C_78)
      | ~ r1_orders_2(k2_yellow_1(A_76),B_77,C_78)
      | ~ m1_subset_1(C_78,A_76)
      | ~ m1_subset_1(B_77,A_76)
      | v2_struct_0(k2_yellow_1(A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_50,c_204])).

tff(c_60,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_123,plain,(
    ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60])).

tff(c_210,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_207,c_123])).

tff(c_213,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68,c_210])).

tff(c_214,plain,(
    ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_217,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_214])).

tff(c_220,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_67,c_68,c_217])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_221])).

tff(c_227,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_227])).

tff(c_230,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_240,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_230])).

tff(c_243,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_243])).

tff(c_246,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_46,plain,(
    ! [A_24] :
      ( ~ v2_struct_0(k2_yellow_1(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_250,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_246,c_46])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_256,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_255,plain,(
    r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_257,plain,(
    ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_257])).

tff(c_298,plain,(
    r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_415,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_orders_2(A_123,B_124,C_125)
      | ~ r3_orders_2(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_417,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ l1_orders_2(k2_yellow_1('#skF_3'))
    | ~ v3_orders_2(k2_yellow_1('#skF_3'))
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_298,c_415])).

tff(c_420,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_67,c_50,c_68,c_50,c_417])).

tff(c_421,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_424,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_46])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_424])).

tff(c_429,plain,(
    r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_390,plain,(
    ! [B_111,C_112,A_113] :
      ( r2_hidden(k4_tarski(B_111,C_112),u1_orders_2(A_113))
      | ~ r1_orders_2(A_113,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_113))
      | ~ m1_subset_1(B_111,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_396,plain,(
    ! [B_111,C_112,A_26] :
      ( r2_hidden(k4_tarski(B_111,C_112),k1_wellord2(A_26))
      | ~ r1_orders_2(k2_yellow_1(A_26),B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(k2_yellow_1(A_26)))
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1(A_26)))
      | ~ l1_orders_2(k2_yellow_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_390])).

tff(c_400,plain,(
    ! [B_114,C_115,A_116] :
      ( r2_hidden(k4_tarski(B_114,C_115),k1_wellord2(A_116))
      | ~ r1_orders_2(k2_yellow_1(A_116),B_114,C_115)
      | ~ m1_subset_1(C_115,A_116)
      | ~ m1_subset_1(B_114,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_50,c_396])).

tff(c_20,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_408,plain,(
    ! [B_114,C_115,A_116] :
      ( r1_tarski(B_114,C_115)
      | ~ r2_hidden(C_115,A_116)
      | ~ r2_hidden(B_114,A_116)
      | ~ r1_orders_2(k2_yellow_1(A_116),B_114,C_115)
      | ~ m1_subset_1(C_115,A_116)
      | ~ m1_subset_1(B_114,A_116) ) ),
    inference(resolution,[status(thm)],[c_400,c_73])).

tff(c_433,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_429,c_408])).

tff(c_436,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68,c_433])).

tff(c_437,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_436])).

tff(c_438,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_446,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_438])).

tff(c_449,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_446])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_449])).

tff(c_452,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_456,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_452])).

tff(c_459,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_456])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  %$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k2_yellow_1 > k1_yellow_1 > k1_wellord2 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.49/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.36  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.49/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.36  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.49/1.36  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.49/1.36  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.49/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.36  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.49/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.49/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.49/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.36  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.49/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.36  
% 2.75/1.38  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.75/1.38  tff(f_101, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.75/1.38  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.75/1.38  tff(f_48, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.75/1.38  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.75/1.38  tff(f_79, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.75/1.38  tff(f_97, axiom, (![A]: (k1_yellow_1(A) = k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_yellow_1)).
% 2.75/1.38  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 2.75/1.38  tff(f_87, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.75/1.38  tff(f_75, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.75/1.38  tff(f_95, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 2.75/1.38  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.38  tff(c_50, plain, (![A_26]: (u1_struct_0(k2_yellow_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.75/1.38  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.38  tff(c_68, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 2.75/1.38  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.38  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.38  tff(c_67, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56])).
% 2.75/1.38  tff(c_66, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.38  tff(c_84, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 2.75/1.38  tff(c_22, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.38  tff(c_18, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.38  tff(c_75, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 2.75/1.38  tff(c_34, plain, (![A_22]: (l1_orders_2(k2_yellow_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.75/1.38  tff(c_48, plain, (![A_25]: (k1_yellow_1(A_25)=k1_wellord2(A_25))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.75/1.38  tff(c_52, plain, (![A_26]: (u1_orders_2(k2_yellow_1(A_26))=k1_yellow_1(A_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.75/1.38  tff(c_69, plain, (![A_26]: (u1_orders_2(k2_yellow_1(A_26))=k1_wellord2(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 2.75/1.38  tff(c_158, plain, (![A_55, B_56, C_57]: (r1_orders_2(A_55, B_56, C_57) | ~r2_hidden(k4_tarski(B_56, C_57), u1_orders_2(A_55)) | ~m1_subset_1(C_57, u1_struct_0(A_55)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.38  tff(c_164, plain, (![A_26, B_56, C_57]: (r1_orders_2(k2_yellow_1(A_26), B_56, C_57) | ~r2_hidden(k4_tarski(B_56, C_57), k1_wellord2(A_26)) | ~m1_subset_1(C_57, u1_struct_0(k2_yellow_1(A_26))) | ~m1_subset_1(B_56, u1_struct_0(k2_yellow_1(A_26))) | ~l1_orders_2(k2_yellow_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_158])).
% 2.75/1.38  tff(c_168, plain, (![A_58, B_59, C_60]: (r1_orders_2(k2_yellow_1(A_58), B_59, C_60) | ~r2_hidden(k4_tarski(B_59, C_60), k1_wellord2(A_58)) | ~m1_subset_1(C_60, A_58) | ~m1_subset_1(B_59, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_50, c_164])).
% 2.75/1.38  tff(c_175, plain, (![A_3, C_9, D_10]: (r1_orders_2(k2_yellow_1(A_3), C_9, D_10) | ~m1_subset_1(D_10, A_3) | ~m1_subset_1(C_9, A_3) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(resolution, [status(thm)], [c_75, c_168])).
% 2.75/1.38  tff(c_38, plain, (![A_23]: (v3_orders_2(k2_yellow_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.38  tff(c_202, plain, (![A_73, B_74, C_75]: (r3_orders_2(A_73, B_74, C_75) | ~r1_orders_2(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.38  tff(c_204, plain, (![A_26, B_74, C_75]: (r3_orders_2(k2_yellow_1(A_26), B_74, C_75) | ~r1_orders_2(k2_yellow_1(A_26), B_74, C_75) | ~m1_subset_1(C_75, A_26) | ~m1_subset_1(B_74, u1_struct_0(k2_yellow_1(A_26))) | ~l1_orders_2(k2_yellow_1(A_26)) | ~v3_orders_2(k2_yellow_1(A_26)) | v2_struct_0(k2_yellow_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_202])).
% 2.75/1.38  tff(c_207, plain, (![A_76, B_77, C_78]: (r3_orders_2(k2_yellow_1(A_76), B_77, C_78) | ~r1_orders_2(k2_yellow_1(A_76), B_77, C_78) | ~m1_subset_1(C_78, A_76) | ~m1_subset_1(B_77, A_76) | v2_struct_0(k2_yellow_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_50, c_204])).
% 2.75/1.38  tff(c_60, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.38  tff(c_123, plain, (~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_60])).
% 2.75/1.38  tff(c_210, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_207, c_123])).
% 2.75/1.38  tff(c_213, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68, c_210])).
% 2.75/1.38  tff(c_214, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_213])).
% 2.75/1.38  tff(c_217, plain, (~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_175, c_214])).
% 2.75/1.38  tff(c_220, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_67, c_68, c_217])).
% 2.75/1.38  tff(c_221, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_220])).
% 2.75/1.38  tff(c_224, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_221])).
% 2.75/1.38  tff(c_227, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_224])).
% 2.75/1.38  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_227])).
% 2.75/1.38  tff(c_230, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_220])).
% 2.75/1.38  tff(c_240, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_230])).
% 2.75/1.38  tff(c_243, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_240])).
% 2.75/1.38  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_243])).
% 2.75/1.38  tff(c_246, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_213])).
% 2.75/1.38  tff(c_46, plain, (![A_24]: (~v2_struct_0(k2_yellow_1(A_24)) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.75/1.38  tff(c_250, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_246, c_46])).
% 2.75/1.38  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_250])).
% 2.75/1.38  tff(c_256, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 2.75/1.38  tff(c_255, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 2.75/1.38  tff(c_257, plain, (~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 2.75/1.38  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_257])).
% 2.75/1.38  tff(c_298, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.75/1.38  tff(c_415, plain, (![A_123, B_124, C_125]: (r1_orders_2(A_123, B_124, C_125) | ~r3_orders_2(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.38  tff(c_417, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3'))) | ~l1_orders_2(k2_yellow_1('#skF_3')) | ~v3_orders_2(k2_yellow_1('#skF_3')) | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_298, c_415])).
% 2.75/1.38  tff(c_420, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_67, c_50, c_68, c_50, c_417])).
% 2.75/1.38  tff(c_421, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_420])).
% 2.75/1.38  tff(c_424, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_421, c_46])).
% 2.75/1.38  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_424])).
% 2.75/1.38  tff(c_429, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_420])).
% 2.75/1.38  tff(c_390, plain, (![B_111, C_112, A_113]: (r2_hidden(k4_tarski(B_111, C_112), u1_orders_2(A_113)) | ~r1_orders_2(A_113, B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(A_113)) | ~m1_subset_1(B_111, u1_struct_0(A_113)) | ~l1_orders_2(A_113))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.38  tff(c_396, plain, (![B_111, C_112, A_26]: (r2_hidden(k4_tarski(B_111, C_112), k1_wellord2(A_26)) | ~r1_orders_2(k2_yellow_1(A_26), B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(k2_yellow_1(A_26))) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1(A_26))) | ~l1_orders_2(k2_yellow_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_390])).
% 2.75/1.38  tff(c_400, plain, (![B_114, C_115, A_116]: (r2_hidden(k4_tarski(B_114, C_115), k1_wellord2(A_116)) | ~r1_orders_2(k2_yellow_1(A_116), B_114, C_115) | ~m1_subset_1(C_115, A_116) | ~m1_subset_1(B_114, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_50, c_396])).
% 2.75/1.38  tff(c_20, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.38  tff(c_73, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 2.75/1.38  tff(c_408, plain, (![B_114, C_115, A_116]: (r1_tarski(B_114, C_115) | ~r2_hidden(C_115, A_116) | ~r2_hidden(B_114, A_116) | ~r1_orders_2(k2_yellow_1(A_116), B_114, C_115) | ~m1_subset_1(C_115, A_116) | ~m1_subset_1(B_114, A_116))), inference(resolution, [status(thm)], [c_400, c_73])).
% 2.75/1.38  tff(c_433, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_429, c_408])).
% 2.75/1.38  tff(c_436, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68, c_433])).
% 2.75/1.38  tff(c_437, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_256, c_436])).
% 2.75/1.38  tff(c_438, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_437])).
% 2.75/1.38  tff(c_446, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_438])).
% 2.75/1.38  tff(c_449, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_446])).
% 2.75/1.38  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_449])).
% 2.75/1.38  tff(c_452, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_437])).
% 2.75/1.38  tff(c_456, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_452])).
% 2.75/1.38  tff(c_459, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_456])).
% 2.75/1.38  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_459])).
% 2.75/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  Inference rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Ref     : 0
% 2.75/1.38  #Sup     : 67
% 2.75/1.38  #Fact    : 0
% 2.75/1.38  #Define  : 0
% 2.75/1.38  #Split   : 6
% 2.75/1.38  #Chain   : 0
% 2.75/1.38  #Close   : 0
% 2.75/1.38  
% 2.75/1.38  Ordering : KBO
% 2.75/1.38  
% 2.75/1.38  Simplification rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Subsume      : 1
% 2.75/1.38  #Demod        : 74
% 2.75/1.38  #Tautology    : 48
% 2.75/1.38  #SimpNegUnit  : 7
% 2.75/1.38  #BackRed      : 0
% 2.75/1.38  
% 2.75/1.38  #Partial instantiations: 0
% 2.75/1.38  #Strategies tried      : 1
% 2.75/1.38  
% 2.75/1.38  Timing (in seconds)
% 2.75/1.38  ----------------------
% 2.75/1.38  Preprocessing        : 0.32
% 2.75/1.38  Parsing              : 0.16
% 2.75/1.38  CNF conversion       : 0.02
% 2.75/1.38  Main loop            : 0.25
% 2.75/1.38  Inferencing          : 0.10
% 2.75/1.38  Reduction            : 0.08
% 2.75/1.38  Demodulation         : 0.06
% 2.75/1.38  BG Simplification    : 0.02
% 2.75/1.38  Subsumption          : 0.03
% 2.75/1.38  Abstraction          : 0.01
% 2.75/1.38  MUC search           : 0.00
% 2.75/1.38  Cooper               : 0.00
% 2.75/1.38  Total                : 0.61
% 2.75/1.38  Index Insertion      : 0.00
% 2.75/1.38  Index Deletion       : 0.00
% 2.75/1.38  Index Matching       : 0.00
% 2.75/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
