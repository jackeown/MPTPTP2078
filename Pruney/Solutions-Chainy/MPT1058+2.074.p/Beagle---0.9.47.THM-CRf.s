%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  83 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_28,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_32] : k2_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [A_47] :
      ( k10_relat_1(A_47,k2_relat_1(A_47)) = k1_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_32] :
      ( k10_relat_1(k6_relat_1(A_32),A_32) = k1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_85,plain,(
    ! [A_32] : k10_relat_1(k6_relat_1(A_32),A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_81])).

tff(c_104,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(k1_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_32,A_53] :
      ( k7_relat_1(k6_relat_1(A_32),A_53) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_53)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_109,plain,(
    ! [A_32,A_53] :
      ( k7_relat_1(k6_relat_1(A_32),A_53) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_107])).

tff(c_128,plain,(
    ! [A_60,C_61,B_62] :
      ( k3_xboole_0(A_60,k10_relat_1(C_61,B_62)) = k10_relat_1(k7_relat_1(C_61,A_60),B_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_137,plain,(
    ! [A_32,A_60] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_32),A_60),A_32) = k3_xboole_0(A_60,A_32)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_128])).

tff(c_145,plain,(
    ! [A_63,A_64] : k10_relat_1(k7_relat_1(k6_relat_1(A_63),A_64),A_63) = k3_xboole_0(A_64,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_137])).

tff(c_157,plain,(
    ! [A_53,A_32] :
      ( k3_xboole_0(A_53,A_32) = k10_relat_1(k6_relat_1(A_32),A_32)
      | ~ r1_tarski(A_32,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_145])).

tff(c_161,plain,(
    ! [A_65,A_66] :
      ( k3_xboole_0(A_65,A_66) = A_66
      | ~ r1_tarski(A_66,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_157])).

tff(c_165,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_26,plain,(
    ! [A_35,C_37,B_36] :
      ( k3_xboole_0(A_35,k10_relat_1(C_37,B_36)) = k10_relat_1(k7_relat_1(C_37,A_35),B_36)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_26])).

tff(c_176,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_169])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.14/1.28  
% 2.31/1.29  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.31/1.29  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.31/1.29  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.31/1.29  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.31/1.29  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.31/1.29  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.31/1.29  tff(c_28, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.29  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.29  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.29  tff(c_16, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.29  tff(c_20, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.29  tff(c_22, plain, (![A_32]: (k2_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.29  tff(c_72, plain, (![A_47]: (k10_relat_1(A_47, k2_relat_1(A_47))=k1_relat_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.29  tff(c_81, plain, (![A_32]: (k10_relat_1(k6_relat_1(A_32), A_32)=k1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_72])).
% 2.31/1.29  tff(c_85, plain, (![A_32]: (k10_relat_1(k6_relat_1(A_32), A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_81])).
% 2.31/1.29  tff(c_104, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(k1_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.29  tff(c_107, plain, (![A_32, A_53]: (k7_relat_1(k6_relat_1(A_32), A_53)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_53) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 2.31/1.29  tff(c_109, plain, (![A_32, A_53]: (k7_relat_1(k6_relat_1(A_32), A_53)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_107])).
% 2.31/1.29  tff(c_128, plain, (![A_60, C_61, B_62]: (k3_xboole_0(A_60, k10_relat_1(C_61, B_62))=k10_relat_1(k7_relat_1(C_61, A_60), B_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.29  tff(c_137, plain, (![A_32, A_60]: (k10_relat_1(k7_relat_1(k6_relat_1(A_32), A_60), A_32)=k3_xboole_0(A_60, A_32) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_128])).
% 2.31/1.29  tff(c_145, plain, (![A_63, A_64]: (k10_relat_1(k7_relat_1(k6_relat_1(A_63), A_64), A_63)=k3_xboole_0(A_64, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_137])).
% 2.31/1.29  tff(c_157, plain, (![A_53, A_32]: (k3_xboole_0(A_53, A_32)=k10_relat_1(k6_relat_1(A_32), A_32) | ~r1_tarski(A_32, A_53))), inference(superposition, [status(thm), theory('equality')], [c_109, c_145])).
% 2.31/1.29  tff(c_161, plain, (![A_65, A_66]: (k3_xboole_0(A_65, A_66)=A_66 | ~r1_tarski(A_66, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_157])).
% 2.31/1.29  tff(c_165, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_161])).
% 2.31/1.29  tff(c_26, plain, (![A_35, C_37, B_36]: (k3_xboole_0(A_35, k10_relat_1(C_37, B_36))=k10_relat_1(k7_relat_1(C_37, A_35), B_36) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.29  tff(c_169, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_165, c_26])).
% 2.31/1.29  tff(c_176, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_169])).
% 2.31/1.29  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_176])).
% 2.31/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  Inference rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Ref     : 0
% 2.31/1.29  #Sup     : 33
% 2.31/1.29  #Fact    : 0
% 2.31/1.29  #Define  : 0
% 2.31/1.29  #Split   : 0
% 2.31/1.29  #Chain   : 0
% 2.31/1.29  #Close   : 0
% 2.31/1.29  
% 2.31/1.29  Ordering : KBO
% 2.31/1.29  
% 2.31/1.29  Simplification rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Subsume      : 0
% 2.31/1.29  #Demod        : 6
% 2.31/1.29  #Tautology    : 23
% 2.31/1.29  #SimpNegUnit  : 1
% 2.31/1.29  #BackRed      : 0
% 2.31/1.29  
% 2.31/1.29  #Partial instantiations: 0
% 2.31/1.29  #Strategies tried      : 1
% 2.31/1.29  
% 2.31/1.29  Timing (in seconds)
% 2.31/1.29  ----------------------
% 2.31/1.29  Preprocessing        : 0.33
% 2.31/1.29  Parsing              : 0.18
% 2.31/1.29  CNF conversion       : 0.02
% 2.31/1.29  Main loop            : 0.14
% 2.31/1.29  Inferencing          : 0.06
% 2.31/1.29  Reduction            : 0.05
% 2.31/1.29  Demodulation         : 0.04
% 2.31/1.29  BG Simplification    : 0.01
% 2.31/1.29  Subsumption          : 0.01
% 2.31/1.29  Abstraction          : 0.01
% 2.31/1.29  MUC search           : 0.00
% 2.31/1.29  Cooper               : 0.00
% 2.31/1.29  Total                : 0.50
% 2.31/1.29  Index Insertion      : 0.00
% 2.31/1.29  Index Deletion       : 0.00
% 2.31/1.29  Index Matching       : 0.00
% 2.31/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
