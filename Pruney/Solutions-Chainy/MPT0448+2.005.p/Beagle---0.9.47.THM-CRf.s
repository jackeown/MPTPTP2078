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
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  53 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_43,B_44,C_45,D_46] : v1_relat_1(k2_tarski(k4_tarski(A_43,B_44),k4_tarski(C_45,D_46))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_43,B_44] : v1_relat_1(k1_tarski(k4_tarski(A_43,B_44))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_tarski(A_53,B_54),k1_tarski(C_55)) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_4,C_55] : k2_xboole_0(k1_tarski(A_4),k1_tarski(C_55)) = k1_enumset1(A_4,A_4,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_114,plain,(
    ! [A_4,C_55] : k2_xboole_0(k1_tarski(A_4),k1_tarski(C_55)) = k2_tarski(A_4,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_20,plain,(
    ! [A_28,B_29,C_30,D_31] : v1_relat_1(k2_tarski(k4_tarski(A_28,B_29),k4_tarski(C_30,D_31))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_32,B_33),k4_tarski(C_34,D_35))) = k2_tarski(A_32,C_34)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_32,B_33),k4_tarski(C_34,D_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_59,B_60,C_61,D_62] : k1_relat_1(k2_tarski(k4_tarski(A_59,B_60),k4_tarski(C_61,D_62))) = k2_tarski(A_59,C_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_157,plain,(
    ! [A_59,B_60] : k2_tarski(A_59,A_59) = k1_relat_1(k1_tarski(k4_tarski(A_59,B_60))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_144])).

tff(c_162,plain,(
    ! [A_59,B_60] : k1_relat_1(k1_tarski(k4_tarski(A_59,B_60))) = k1_tarski(A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_22,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_32,B_33),k4_tarski(C_34,D_35))) = k2_tarski(B_33,D_35)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_32,B_33),k4_tarski(C_34,D_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_177,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_relat_1(k2_tarski(k4_tarski(A_65,B_66),k4_tarski(C_67,D_68))) = k2_tarski(B_66,D_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_190,plain,(
    ! [B_66,A_65] : k2_tarski(B_66,B_66) = k2_relat_1(k1_tarski(k4_tarski(A_65,B_66))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_177])).

tff(c_196,plain,(
    ! [A_69,B_70] : k2_relat_1(k1_tarski(k4_tarski(A_69,B_70))) = k1_tarski(B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_18,plain,(
    ! [A_27] :
      ( k2_xboole_0(k1_relat_1(A_27),k2_relat_1(A_27)) = k3_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(A_69,B_70))),k1_tarski(B_70)) = k3_relat_1(k1_tarski(k4_tarski(A_69,B_70)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_69,B_70))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_18])).

tff(c_208,plain,(
    ! [A_69,B_70] : k3_relat_1(k1_tarski(k4_tarski(A_69,B_70))) = k2_tarski(A_69,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_114,c_162,c_202])).

tff(c_26,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.95/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.22  
% 1.95/1.24  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.24  tff(f_47, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.95/1.24  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.24  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.95/1.24  tff(f_55, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 1.95/1.24  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.95/1.24  tff(f_58, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 1.95/1.24  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.24  tff(c_78, plain, (![A_43, B_44, C_45, D_46]: (v1_relat_1(k2_tarski(k4_tarski(A_43, B_44), k4_tarski(C_45, D_46))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.24  tff(c_82, plain, (![A_43, B_44]: (v1_relat_1(k1_tarski(k4_tarski(A_43, B_44))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78])).
% 1.95/1.24  tff(c_6, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_102, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_tarski(A_53, B_54), k1_tarski(C_55))=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.24  tff(c_111, plain, (![A_4, C_55]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(C_55))=k1_enumset1(A_4, A_4, C_55))), inference(superposition, [status(thm), theory('equality')], [c_4, c_102])).
% 1.95/1.24  tff(c_114, plain, (![A_4, C_55]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(C_55))=k2_tarski(A_4, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 1.95/1.24  tff(c_20, plain, (![A_28, B_29, C_30, D_31]: (v1_relat_1(k2_tarski(k4_tarski(A_28, B_29), k4_tarski(C_30, D_31))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.24  tff(c_24, plain, (![A_32, B_33, C_34, D_35]: (k1_relat_1(k2_tarski(k4_tarski(A_32, B_33), k4_tarski(C_34, D_35)))=k2_tarski(A_32, C_34) | ~v1_relat_1(k2_tarski(k4_tarski(A_32, B_33), k4_tarski(C_34, D_35))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.24  tff(c_144, plain, (![A_59, B_60, C_61, D_62]: (k1_relat_1(k2_tarski(k4_tarski(A_59, B_60), k4_tarski(C_61, D_62)))=k2_tarski(A_59, C_61))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 1.95/1.24  tff(c_157, plain, (![A_59, B_60]: (k2_tarski(A_59, A_59)=k1_relat_1(k1_tarski(k4_tarski(A_59, B_60))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_144])).
% 1.95/1.24  tff(c_162, plain, (![A_59, B_60]: (k1_relat_1(k1_tarski(k4_tarski(A_59, B_60)))=k1_tarski(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_157])).
% 1.95/1.24  tff(c_22, plain, (![A_32, B_33, C_34, D_35]: (k2_relat_1(k2_tarski(k4_tarski(A_32, B_33), k4_tarski(C_34, D_35)))=k2_tarski(B_33, D_35) | ~v1_relat_1(k2_tarski(k4_tarski(A_32, B_33), k4_tarski(C_34, D_35))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.24  tff(c_177, plain, (![A_65, B_66, C_67, D_68]: (k2_relat_1(k2_tarski(k4_tarski(A_65, B_66), k4_tarski(C_67, D_68)))=k2_tarski(B_66, D_68))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 1.95/1.24  tff(c_190, plain, (![B_66, A_65]: (k2_tarski(B_66, B_66)=k2_relat_1(k1_tarski(k4_tarski(A_65, B_66))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_177])).
% 1.95/1.24  tff(c_196, plain, (![A_69, B_70]: (k2_relat_1(k1_tarski(k4_tarski(A_69, B_70)))=k1_tarski(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_190])).
% 1.95/1.24  tff(c_18, plain, (![A_27]: (k2_xboole_0(k1_relat_1(A_27), k2_relat_1(A_27))=k3_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.24  tff(c_202, plain, (![A_69, B_70]: (k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(A_69, B_70))), k1_tarski(B_70))=k3_relat_1(k1_tarski(k4_tarski(A_69, B_70))) | ~v1_relat_1(k1_tarski(k4_tarski(A_69, B_70))))), inference(superposition, [status(thm), theory('equality')], [c_196, c_18])).
% 1.95/1.24  tff(c_208, plain, (![A_69, B_70]: (k3_relat_1(k1_tarski(k4_tarski(A_69, B_70)))=k2_tarski(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_114, c_162, c_202])).
% 1.95/1.24  tff(c_26, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.24  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_26])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 39
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 0
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 0
% 1.95/1.24  #Demod        : 16
% 1.95/1.24  #Tautology    : 29
% 1.95/1.24  #SimpNegUnit  : 0
% 1.95/1.24  #BackRed      : 1
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.24  Preprocessing        : 0.32
% 1.95/1.24  Parsing              : 0.17
% 1.95/1.24  CNF conversion       : 0.02
% 1.95/1.24  Main loop            : 0.13
% 1.95/1.24  Inferencing          : 0.05
% 1.95/1.24  Reduction            : 0.05
% 1.95/1.24  Demodulation         : 0.04
% 1.95/1.24  BG Simplification    : 0.01
% 1.95/1.24  Subsumption          : 0.01
% 1.95/1.24  Abstraction          : 0.01
% 1.95/1.24  MUC search           : 0.00
% 1.95/1.24  Cooper               : 0.00
% 1.95/1.24  Total                : 0.47
% 2.03/1.24  Index Insertion      : 0.00
% 2.03/1.24  Index Deletion       : 0.00
% 2.03/1.24  Index Matching       : 0.00
% 2.03/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
