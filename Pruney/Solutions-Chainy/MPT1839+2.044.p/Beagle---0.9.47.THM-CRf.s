%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  71 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_3,B_4] : k4_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(A_47,B_46)
      | ~ v1_zfmisc_1(B_46)
      | v1_xboole_0(B_46)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ v1_zfmisc_1(B_48)
      | v1_xboole_0(B_48)
      | v1_xboole_0(A_49)
      | k4_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_124])).

tff(c_135,plain,(
    ! [A_49] :
      ( A_49 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_49)
      | k4_xboole_0(A_49,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_139,plain,(
    ! [A_50] :
      ( A_50 = '#skF_1'
      | v1_xboole_0(A_50)
      | k4_xboole_0(A_50,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_135])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_26])).

tff(c_148,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_142])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_12])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_157])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.89/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.89/1.19  
% 1.93/1.20  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.93/1.20  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 1.93/1.20  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.93/1.20  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.93/1.20  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.93/1.20  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.93/1.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.93/1.20  tff(c_63, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.93/1.20  tff(c_71, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_24])).
% 1.93/1.20  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.20  tff(c_41, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k2_xboole_0(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.20  tff(c_48, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 1.93/1.20  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_58, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_62, plain, (![A_3, B_4]: (k4_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.93/1.20  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.93/1.20  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.93/1.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_124, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(A_47, B_46) | ~v1_zfmisc_1(B_46) | v1_xboole_0(B_46) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.20  tff(c_133, plain, (![B_48, A_49]: (B_48=A_49 | ~v1_zfmisc_1(B_48) | v1_xboole_0(B_48) | v1_xboole_0(A_49) | k4_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_124])).
% 1.93/1.20  tff(c_135, plain, (![A_49]: (A_49='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_49) | k4_xboole_0(A_49, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_133])).
% 1.93/1.20  tff(c_139, plain, (![A_50]: (A_50='#skF_1' | v1_xboole_0(A_50) | k4_xboole_0(A_50, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_135])).
% 1.93/1.20  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.93/1.20  tff(c_142, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_26])).
% 1.93/1.20  tff(c_148, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_142])).
% 1.93/1.20  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.20  tff(c_157, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_148, c_12])).
% 1.93/1.20  tff(c_166, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_157])).
% 1.93/1.20  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_166])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 32
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 1
% 1.93/1.20  #Demod        : 4
% 1.93/1.20  #Tautology    : 21
% 1.93/1.20  #SimpNegUnit  : 2
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.30
% 1.93/1.20  Parsing              : 0.17
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.13
% 1.93/1.20  Inferencing          : 0.06
% 1.93/1.20  Reduction            : 0.04
% 1.93/1.20  Demodulation         : 0.02
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.02
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.46
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
