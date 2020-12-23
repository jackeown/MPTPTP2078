%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 321 expanded)
%              Number of leaves         :   25 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  144 ( 635 expanded)
%              Number of equality atoms :   39 ( 122 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_109,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_29,B_30)),k1_relat_1(A_29))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    ! [B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_30)),k1_xboole_0)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_109])).

tff(c_118,plain,(
    ! [B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_31)),k1_xboole_0)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_114])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_149,plain,(
    ! [B_34] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_34)) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_118,c_95])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [B_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_20])).

tff(c_175,plain,(
    ! [B_35] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_184,plain,(
    ! [B_36] :
      ( k5_relat_1(k1_xboole_0,B_36) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_188,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_184])).

tff(c_192,plain,(
    ! [B_37] :
      ( k5_relat_1(k1_xboole_0,B_37) = k1_xboole_0
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_188])).

tff(c_204,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_192])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_204])).

tff(c_212,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_274,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_46,B_47)),k1_relat_1(A_46))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_282,plain,(
    ! [B_47] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_47)),k1_xboole_0)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_274])).

tff(c_288,plain,(
    ! [B_48] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_48)),k1_xboole_0)
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_282])).

tff(c_245,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_254,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_324,plain,(
    ! [B_51] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_51)) = k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_288,c_254])).

tff(c_339,plain,(
    ! [B_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_51))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_20])).

tff(c_355,plain,(
    ! [B_52] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_52))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_339])).

tff(c_369,plain,(
    ! [B_53] :
      ( k5_relat_1(k1_xboole_0,B_53) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_355,c_4])).

tff(c_373,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_382,plain,(
    ! [B_54] :
      ( k5_relat_1(k1_xboole_0,B_54) = k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_373])).

tff(c_396,plain,(
    ! [A_6] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_6)) = k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_382])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_303,plain,(
    ! [B_49,A_50] :
      ( k5_relat_1(k4_relat_1(B_49),k4_relat_1(A_50)) = k4_relat_1(k5_relat_1(A_50,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_550,plain,(
    ! [A_60,A_61] :
      ( k4_relat_1(k5_relat_1(A_60,k4_relat_1(A_61))) = k5_relat_1(A_61,k4_relat_1(A_60))
      | ~ v1_relat_1(k4_relat_1(A_61))
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_303])).

tff(c_583,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_550])).

tff(c_594,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_583])).

tff(c_609,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_16,c_594])).

tff(c_625,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_396])).

tff(c_663,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_625])).

tff(c_608,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_594])).

tff(c_715,plain,(
    ! [A_64] :
      ( k5_relat_1(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_663,c_608])).

tff(c_730,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_715])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.29/1.34  
% 2.29/1.34  %Foreground sorts:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Background operators:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Foreground operators:
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.29/1.34  
% 2.29/1.36  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.29/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.36  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.29/1.36  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.29/1.36  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.29/1.36  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.29/1.36  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.29/1.36  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.36  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.29/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.29/1.36  tff(f_46, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.29/1.36  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.29/1.36  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.29/1.36  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.29/1.36  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.29/1.36  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.29/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.29/1.36  tff(c_52, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.36  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.29/1.36  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.36  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.36  tff(c_109, plain, (![A_29, B_30]: (r1_tarski(k1_relat_1(k5_relat_1(A_29, B_30)), k1_relat_1(A_29)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.36  tff(c_114, plain, (![B_30]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_30)), k1_xboole_0) | ~v1_relat_1(B_30) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_109])).
% 2.29/1.36  tff(c_118, plain, (![B_31]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_31)), k1_xboole_0) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_114])).
% 2.29/1.36  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.36  tff(c_86, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.29/1.36  tff(c_95, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.29/1.36  tff(c_149, plain, (![B_34]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_34))=k1_xboole_0 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_118, c_95])).
% 2.29/1.36  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.36  tff(c_164, plain, (![B_34]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_149, c_20])).
% 2.29/1.36  tff(c_175, plain, (![B_35]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_164])).
% 2.29/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.29/1.36  tff(c_184, plain, (![B_36]: (k5_relat_1(k1_xboole_0, B_36)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_175, c_4])).
% 2.29/1.36  tff(c_188, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_184])).
% 2.29/1.36  tff(c_192, plain, (![B_37]: (k5_relat_1(k1_xboole_0, B_37)=k1_xboole_0 | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_188])).
% 2.29/1.36  tff(c_204, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_192])).
% 2.29/1.36  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_204])).
% 2.29/1.36  tff(c_212, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.29/1.36  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.36  tff(c_274, plain, (![A_46, B_47]: (r1_tarski(k1_relat_1(k5_relat_1(A_46, B_47)), k1_relat_1(A_46)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.36  tff(c_282, plain, (![B_47]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_47)), k1_xboole_0) | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_274])).
% 2.29/1.36  tff(c_288, plain, (![B_48]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_48)), k1_xboole_0) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_282])).
% 2.29/1.36  tff(c_245, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.29/1.36  tff(c_254, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_245])).
% 2.29/1.36  tff(c_324, plain, (![B_51]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_51))=k1_xboole_0 | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_288, c_254])).
% 2.29/1.36  tff(c_339, plain, (![B_51]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_51)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_51)) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_324, c_20])).
% 2.29/1.36  tff(c_355, plain, (![B_52]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_52)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_52)) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_339])).
% 2.29/1.36  tff(c_369, plain, (![B_53]: (k5_relat_1(k1_xboole_0, B_53)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_53)) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_355, c_4])).
% 2.29/1.36  tff(c_373, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_369])).
% 2.29/1.36  tff(c_382, plain, (![B_54]: (k5_relat_1(k1_xboole_0, B_54)=k1_xboole_0 | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_373])).
% 2.29/1.36  tff(c_396, plain, (![A_6]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_6))=k1_xboole_0 | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_382])).
% 2.29/1.36  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.36  tff(c_303, plain, (![B_49, A_50]: (k5_relat_1(k4_relat_1(B_49), k4_relat_1(A_50))=k4_relat_1(k5_relat_1(A_50, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.29/1.36  tff(c_550, plain, (![A_60, A_61]: (k4_relat_1(k5_relat_1(A_60, k4_relat_1(A_61)))=k5_relat_1(A_61, k4_relat_1(A_60)) | ~v1_relat_1(k4_relat_1(A_61)) | ~v1_relat_1(A_60) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_22, c_303])).
% 2.29/1.36  tff(c_583, plain, (![A_6]: (k5_relat_1(A_6, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_396, c_550])).
% 2.29/1.36  tff(c_594, plain, (![A_62]: (k5_relat_1(A_62, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_62)) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_583])).
% 2.29/1.36  tff(c_609, plain, (![A_63]: (k5_relat_1(A_63, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_16, c_594])).
% 2.29/1.36  tff(c_625, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_609, c_396])).
% 2.29/1.36  tff(c_663, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_625])).
% 2.29/1.36  tff(c_608, plain, (![A_6]: (k5_relat_1(A_6, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_594])).
% 2.29/1.36  tff(c_715, plain, (![A_64]: (k5_relat_1(A_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_663, c_608])).
% 2.29/1.36  tff(c_730, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_715])).
% 2.29/1.36  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_730])).
% 2.29/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.36  
% 2.29/1.36  Inference rules
% 2.29/1.36  ----------------------
% 2.29/1.36  #Ref     : 0
% 2.29/1.36  #Sup     : 158
% 2.29/1.36  #Fact    : 0
% 2.29/1.36  #Define  : 0
% 2.29/1.36  #Split   : 1
% 2.29/1.36  #Chain   : 0
% 2.29/1.36  #Close   : 0
% 2.29/1.36  
% 2.29/1.36  Ordering : KBO
% 2.29/1.36  
% 2.29/1.36  Simplification rules
% 2.29/1.36  ----------------------
% 2.29/1.36  #Subsume      : 10
% 2.29/1.36  #Demod        : 123
% 2.29/1.36  #Tautology    : 90
% 2.29/1.36  #SimpNegUnit  : 2
% 2.29/1.36  #BackRed      : 1
% 2.29/1.36  
% 2.29/1.36  #Partial instantiations: 0
% 2.29/1.36  #Strategies tried      : 1
% 2.29/1.36  
% 2.29/1.36  Timing (in seconds)
% 2.29/1.36  ----------------------
% 2.29/1.36  Preprocessing        : 0.28
% 2.29/1.36  Parsing              : 0.15
% 2.29/1.36  CNF conversion       : 0.02
% 2.29/1.36  Main loop            : 0.31
% 2.29/1.36  Inferencing          : 0.12
% 2.29/1.36  Reduction            : 0.09
% 2.29/1.36  Demodulation         : 0.06
% 2.29/1.36  BG Simplification    : 0.02
% 2.29/1.36  Subsumption          : 0.06
% 2.29/1.36  Abstraction          : 0.02
% 2.29/1.36  MUC search           : 0.00
% 2.29/1.36  Cooper               : 0.00
% 2.29/1.36  Total                : 0.63
% 2.29/1.36  Index Insertion      : 0.00
% 2.29/1.36  Index Deletion       : 0.00
% 2.29/1.36  Index Matching       : 0.00
% 2.29/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
