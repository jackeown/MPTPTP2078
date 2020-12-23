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
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 160 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 287 expanded)
%              Number of equality atoms :   38 (  92 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_28])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_45,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_109,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_109])).

tff(c_125,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_121])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_195,plain,(
    ! [B_46,A_47] :
      ( k1_relat_1(k7_relat_1(B_46,A_47)) = A_47
      | ~ r1_tarski(A_47,k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_210,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_202])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_215,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_24])).

tff(c_251,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_254,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_254])).

tff(c_260,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_22,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_313,plain,(
    ! [A_52,C_53,B_54] :
      ( k3_xboole_0(A_52,k10_relat_1(C_53,B_54)) = k10_relat_1(k7_relat_1(C_53,A_52),B_54)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_412,plain,(
    ! [C_58,B_59] :
      ( k10_relat_1(k7_relat_1(C_58,k10_relat_1(C_58,B_59)),B_59) = k10_relat_1(C_58,B_59)
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_313])).

tff(c_562,plain,(
    ! [A_69] :
      ( k10_relat_1(k7_relat_1(A_69,k1_relat_1(A_69)),k2_relat_1(A_69)) = k10_relat_1(A_69,k2_relat_1(A_69))
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_412])).

tff(c_605,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_562])).

tff(c_616,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_605])).

tff(c_329,plain,(
    ! [A_15,A_52] :
      ( k10_relat_1(k7_relat_1(A_15,A_52),k2_relat_1(A_15)) = k3_xboole_0(A_52,k1_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_313])).

tff(c_652,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_329])).

tff(c_670,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_53,c_210,c_652])).

tff(c_700,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_670])).

tff(c_717,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_700])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_319,plain,(
    ! [A_52,C_53,B_54] :
      ( k5_xboole_0(A_52,k10_relat_1(k7_relat_1(C_53,A_52),B_54)) = k4_xboole_0(A_52,k10_relat_1(C_53,B_54))
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_12])).

tff(c_726,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_319])).

tff(c_741,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_125,c_726])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.79  
% 3.04/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.79  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.04/1.79  
% 3.04/1.79  %Foreground sorts:
% 3.04/1.79  
% 3.04/1.79  
% 3.04/1.79  %Background operators:
% 3.04/1.79  
% 3.04/1.79  
% 3.04/1.79  %Foreground operators:
% 3.04/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.04/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.04/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.04/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.79  
% 3.04/1.81  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.04/1.81  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.04/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.81  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.81  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.04/1.81  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.04/1.81  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.04/1.81  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.04/1.81  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.04/1.81  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.04/1.81  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.81  tff(c_28, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.04/1.81  tff(c_75, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_28])).
% 3.04/1.81  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.04/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.81  tff(c_76, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.81  tff(c_88, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.04/1.81  tff(c_45, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.81  tff(c_53, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_45])).
% 3.04/1.81  tff(c_109, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.81  tff(c_121, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_53, c_109])).
% 3.04/1.81  tff(c_125, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_121])).
% 3.04/1.81  tff(c_20, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.04/1.81  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.81  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.04/1.81  tff(c_195, plain, (![B_46, A_47]: (k1_relat_1(k7_relat_1(B_46, A_47))=A_47 | ~r1_tarski(A_47, k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.81  tff(c_202, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_195])).
% 3.04/1.81  tff(c_210, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_202])).
% 3.04/1.81  tff(c_24, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.81  tff(c_215, plain, (![A_16]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_210, c_24])).
% 3.04/1.81  tff(c_251, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_215])).
% 3.04/1.81  tff(c_254, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_251])).
% 3.04/1.81  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_254])).
% 3.04/1.81  tff(c_260, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_215])).
% 3.04/1.81  tff(c_22, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.81  tff(c_313, plain, (![A_52, C_53, B_54]: (k3_xboole_0(A_52, k10_relat_1(C_53, B_54))=k10_relat_1(k7_relat_1(C_53, A_52), B_54) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.04/1.81  tff(c_412, plain, (![C_58, B_59]: (k10_relat_1(k7_relat_1(C_58, k10_relat_1(C_58, B_59)), B_59)=k10_relat_1(C_58, B_59) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_53, c_313])).
% 3.04/1.81  tff(c_562, plain, (![A_69]: (k10_relat_1(k7_relat_1(A_69, k1_relat_1(A_69)), k2_relat_1(A_69))=k10_relat_1(A_69, k2_relat_1(A_69)) | ~v1_relat_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_22, c_412])).
% 3.04/1.81  tff(c_605, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_562])).
% 3.04/1.81  tff(c_616, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_605])).
% 3.04/1.81  tff(c_329, plain, (![A_15, A_52]: (k10_relat_1(k7_relat_1(A_15, A_52), k2_relat_1(A_15))=k3_xboole_0(A_52, k1_relat_1(A_15)) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_313])).
% 3.04/1.81  tff(c_652, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_329])).
% 3.04/1.81  tff(c_670, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_53, c_210, c_652])).
% 3.04/1.81  tff(c_700, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_670])).
% 3.04/1.81  tff(c_717, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_700])).
% 3.04/1.81  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.81  tff(c_319, plain, (![A_52, C_53, B_54]: (k5_xboole_0(A_52, k10_relat_1(k7_relat_1(C_53, A_52), B_54))=k4_xboole_0(A_52, k10_relat_1(C_53, B_54)) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_313, c_12])).
% 3.04/1.81  tff(c_726, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_717, c_319])).
% 3.04/1.81  tff(c_741, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_125, c_726])).
% 3.04/1.81  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_741])).
% 3.04/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.81  
% 3.04/1.81  Inference rules
% 3.04/1.81  ----------------------
% 3.04/1.81  #Ref     : 0
% 3.04/1.81  #Sup     : 174
% 3.04/1.81  #Fact    : 0
% 3.04/1.81  #Define  : 0
% 3.04/1.81  #Split   : 3
% 3.04/1.81  #Chain   : 0
% 3.04/1.81  #Close   : 0
% 3.04/1.81  
% 3.04/1.81  Ordering : KBO
% 3.04/1.81  
% 3.04/1.81  Simplification rules
% 3.04/1.81  ----------------------
% 3.04/1.81  #Subsume      : 6
% 3.04/1.81  #Demod        : 91
% 3.04/1.81  #Tautology    : 82
% 3.04/1.81  #SimpNegUnit  : 1
% 3.04/1.81  #BackRed      : 1
% 3.04/1.81  
% 3.04/1.81  #Partial instantiations: 0
% 3.04/1.81  #Strategies tried      : 1
% 3.04/1.81  
% 3.04/1.81  Timing (in seconds)
% 3.04/1.81  ----------------------
% 3.04/1.81  Preprocessing        : 0.46
% 3.04/1.81  Parsing              : 0.24
% 3.04/1.81  CNF conversion       : 0.03
% 3.04/1.81  Main loop            : 0.44
% 3.04/1.81  Inferencing          : 0.17
% 3.04/1.81  Reduction            : 0.13
% 3.04/1.81  Demodulation         : 0.09
% 3.04/1.81  BG Simplification    : 0.03
% 3.04/1.81  Subsumption          : 0.09
% 3.04/1.81  Abstraction          : 0.03
% 3.04/1.81  MUC search           : 0.00
% 3.04/1.81  Cooper               : 0.00
% 3.04/1.81  Total                : 0.94
% 3.04/1.81  Index Insertion      : 0.00
% 3.04/1.81  Index Deletion       : 0.00
% 3.04/1.81  Index Matching       : 0.00
% 3.04/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
