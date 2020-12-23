%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  54 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  64 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k3_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_31,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_72,axiom,(
    ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_46,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_28] :
      ( v1_relat_1(A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ! [A_49,B_50,C_51,D_52] : v1_relat_1(k2_tarski(k4_tarski(A_49,B_50),k4_tarski(C_51,D_52))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    ! [A_49,B_50] : v1_relat_1(k1_tarski(k4_tarski(A_49,B_50))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_117])).

tff(c_44,plain,(
    ! [A_25,B_26] : k3_relat_1(k1_tarski(k4_tarski(A_25,B_26))) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k3_relat_1(A_65),k3_relat_1(B_66))
      | ~ r1_tarski(A_65,B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    ! [A_65,A_25,B_26] :
      ( r1_tarski(k3_relat_1(A_65),k2_tarski(A_25,B_26))
      | ~ r1_tarski(A_65,k1_tarski(k4_tarski(A_25,B_26)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_25,B_26)))
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_225,plain,(
    ! [A_77,A_78,B_79] :
      ( r1_tarski(k3_relat_1(A_77),k2_tarski(A_78,B_79))
      | ~ r1_tarski(A_77,k1_tarski(k4_tarski(A_78,B_79)))
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_187])).

tff(c_238,plain,(
    ! [A_80,A_81] :
      ( r1_tarski(k3_relat_1(A_80),k1_tarski(A_81))
      | ~ r1_tarski(A_80,k1_tarski(k4_tarski(A_81,A_81)))
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_225])).

tff(c_244,plain,(
    ! [A_81] :
      ( r1_tarski(k3_relat_1(k1_xboole_0),k1_tarski(A_81))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_238])).

tff(c_249,plain,(
    ! [A_82] : r1_tarski(k3_relat_1(k1_xboole_0),k1_tarski(A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_258,plain,(
    ! [A_83] : k4_xboole_0(k3_relat_1(k1_xboole_0),k1_tarski(A_83)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_249,c_8])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,k1_tarski(B_16)) = A_15
      | r2_hidden(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_263,plain,(
    ! [A_83] :
      ( k3_relat_1(k1_xboole_0) = k1_xboole_0
      | r2_hidden(A_83,k3_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_36])).

tff(c_277,plain,(
    ! [A_84] : r2_hidden(A_84,k3_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_263])).

tff(c_16,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_80,plain,(
    ! [D_11,B_7] : ~ r2_hidden(k2_tarski(D_11,B_7),D_11) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_295,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_277,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k3_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.28  
% 2.06/1.30  tff(f_74, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 2.06/1.30  tff(f_31, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.30  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.06/1.30  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.06/1.30  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.30  tff(f_61, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.06/1.30  tff(f_72, axiom, (![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 2.06/1.30  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.06/1.30  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.06/1.30  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.06/1.30  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.30  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.06/1.30  tff(c_46, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.30  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.30  tff(c_48, plain, (![A_28]: (v1_relat_1(A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.30  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_48])).
% 2.06/1.30  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.30  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.30  tff(c_117, plain, (![A_49, B_50, C_51, D_52]: (v1_relat_1(k2_tarski(k4_tarski(A_49, B_50), k4_tarski(C_51, D_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.30  tff(c_121, plain, (![A_49, B_50]: (v1_relat_1(k1_tarski(k4_tarski(A_49, B_50))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_117])).
% 2.06/1.30  tff(c_44, plain, (![A_25, B_26]: (k3_relat_1(k1_tarski(k4_tarski(A_25, B_26)))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.06/1.30  tff(c_178, plain, (![A_65, B_66]: (r1_tarski(k3_relat_1(A_65), k3_relat_1(B_66)) | ~r1_tarski(A_65, B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.30  tff(c_187, plain, (![A_65, A_25, B_26]: (r1_tarski(k3_relat_1(A_65), k2_tarski(A_25, B_26)) | ~r1_tarski(A_65, k1_tarski(k4_tarski(A_25, B_26))) | ~v1_relat_1(k1_tarski(k4_tarski(A_25, B_26))) | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_44, c_178])).
% 2.06/1.30  tff(c_225, plain, (![A_77, A_78, B_79]: (r1_tarski(k3_relat_1(A_77), k2_tarski(A_78, B_79)) | ~r1_tarski(A_77, k1_tarski(k4_tarski(A_78, B_79))) | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_187])).
% 2.06/1.30  tff(c_238, plain, (![A_80, A_81]: (r1_tarski(k3_relat_1(A_80), k1_tarski(A_81)) | ~r1_tarski(A_80, k1_tarski(k4_tarski(A_81, A_81))) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_30, c_225])).
% 2.06/1.30  tff(c_244, plain, (![A_81]: (r1_tarski(k3_relat_1(k1_xboole_0), k1_tarski(A_81)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_238])).
% 2.06/1.30  tff(c_249, plain, (![A_82]: (r1_tarski(k3_relat_1(k1_xboole_0), k1_tarski(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 2.06/1.30  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.30  tff(c_258, plain, (![A_83]: (k4_xboole_0(k3_relat_1(k1_xboole_0), k1_tarski(A_83))=k1_xboole_0)), inference(resolution, [status(thm)], [c_249, c_8])).
% 2.06/1.30  tff(c_36, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k1_tarski(B_16))=A_15 | r2_hidden(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.30  tff(c_263, plain, (![A_83]: (k3_relat_1(k1_xboole_0)=k1_xboole_0 | r2_hidden(A_83, k3_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_36])).
% 2.06/1.30  tff(c_277, plain, (![A_84]: (r2_hidden(A_84, k3_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_46, c_263])).
% 2.06/1.30  tff(c_16, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.30  tff(c_71, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.06/1.30  tff(c_80, plain, (![D_11, B_7]: (~r2_hidden(k2_tarski(D_11, B_7), D_11))), inference(resolution, [status(thm)], [c_16, c_71])).
% 2.06/1.30  tff(c_295, plain, $false, inference(resolution, [status(thm)], [c_277, c_80])).
% 2.06/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  Inference rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Ref     : 0
% 2.06/1.30  #Sup     : 54
% 2.06/1.30  #Fact    : 0
% 2.06/1.30  #Define  : 0
% 2.06/1.30  #Split   : 0
% 2.06/1.30  #Chain   : 0
% 2.06/1.30  #Close   : 0
% 2.06/1.30  
% 2.06/1.30  Ordering : KBO
% 2.06/1.30  
% 2.06/1.30  Simplification rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Subsume      : 3
% 2.06/1.30  #Demod        : 7
% 2.06/1.30  #Tautology    : 22
% 2.06/1.30  #SimpNegUnit  : 4
% 2.06/1.30  #BackRed      : 0
% 2.06/1.30  
% 2.06/1.30  #Partial instantiations: 0
% 2.06/1.30  #Strategies tried      : 1
% 2.06/1.30  
% 2.06/1.30  Timing (in seconds)
% 2.06/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.30
% 2.24/1.30  Parsing              : 0.15
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.19
% 2.24/1.30  Inferencing          : 0.07
% 2.24/1.30  Reduction            : 0.06
% 2.24/1.30  Demodulation         : 0.04
% 2.24/1.30  BG Simplification    : 0.01
% 2.24/1.30  Subsumption          : 0.04
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.51
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
