%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   58 (  64 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  73 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k3_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    r1_setfam_1('#skF_7',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_40] : k1_setfam_1(k1_tarski(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = k1_setfam_1(k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_127,plain,(
    ! [A_57] : k3_xboole_0(A_57,A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_114])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [A_57] : k2_xboole_0(A_57,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_76,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_139,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_85])).

tff(c_158,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k3_tarski(A_60),k3_tarski(B_61))
      | ~ r1_setfam_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,(
    ! [A_60,A_8] :
      ( r1_tarski(k3_tarski(A_60),A_8)
      | ~ r1_setfam_1(A_60,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_158])).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_218,plain,(
    ! [C_79,A_80,D_81] :
      ( r2_hidden(C_79,k3_tarski(A_80))
      | ~ r2_hidden(D_81,A_80)
      | ~ r2_hidden(C_79,D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_237,plain,(
    ! [C_85] :
      ( r2_hidden(C_85,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_85,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_267,plain,(
    ! [C_88,B_89] :
      ( r2_hidden(C_88,B_89)
      | ~ r1_tarski(k3_tarski('#skF_7'),B_89)
      | ~ r2_hidden(C_88,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_237,c_2])).

tff(c_340,plain,(
    ! [C_97,A_98] :
      ( r2_hidden(C_97,A_98)
      | ~ r2_hidden(C_97,'#skF_8')
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_98)) ) ),
    inference(resolution,[status(thm)],[c_164,c_267])).

tff(c_766,plain,(
    ! [B_177,A_178] :
      ( r2_hidden('#skF_1'('#skF_8',B_177),A_178)
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_178))
      | r1_tarski('#skF_8',B_177) ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_804,plain,(
    ! [A_179] :
      ( ~ r1_setfam_1('#skF_7',k1_tarski(A_179))
      | r1_tarski('#skF_8',A_179) ) ),
    inference(resolution,[status(thm)],[c_766,c_4])).

tff(c_807,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_804])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k3_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.02/1.47  
% 3.02/1.47  %Foreground sorts:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Background operators:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Foreground operators:
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.47  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.02/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.02/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.02/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.47  
% 3.02/1.48  tff(f_70, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 3.02/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.02/1.48  tff(f_56, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.02/1.48  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.02/1.48  tff(f_58, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.02/1.48  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.02/1.48  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.02/1.48  tff(f_62, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 3.02/1.48  tff(f_52, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.02/1.48  tff(c_44, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.48  tff(c_48, plain, (r1_setfam_1('#skF_7', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.48  tff(c_38, plain, (![A_40]: (k1_setfam_1(k1_tarski(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.48  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.48  tff(c_105, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.02/1.48  tff(c_114, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=k1_setfam_1(k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 3.02/1.48  tff(c_127, plain, (![A_57]: (k3_xboole_0(A_57, A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_114])).
% 3.02/1.48  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.48  tff(c_133, plain, (![A_57]: (k2_xboole_0(A_57, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 3.02/1.48  tff(c_76, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.02/1.48  tff(c_85, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_76])).
% 3.02/1.48  tff(c_139, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_85])).
% 3.02/1.48  tff(c_158, plain, (![A_60, B_61]: (r1_tarski(k3_tarski(A_60), k3_tarski(B_61)) | ~r1_setfam_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.48  tff(c_164, plain, (![A_60, A_8]: (r1_tarski(k3_tarski(A_60), A_8) | ~r1_setfam_1(A_60, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_158])).
% 3.02/1.48  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.48  tff(c_218, plain, (![C_79, A_80, D_81]: (r2_hidden(C_79, k3_tarski(A_80)) | ~r2_hidden(D_81, A_80) | ~r2_hidden(C_79, D_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.48  tff(c_237, plain, (![C_85]: (r2_hidden(C_85, k3_tarski('#skF_7')) | ~r2_hidden(C_85, '#skF_8'))), inference(resolution, [status(thm)], [c_46, c_218])).
% 3.02/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.48  tff(c_267, plain, (![C_88, B_89]: (r2_hidden(C_88, B_89) | ~r1_tarski(k3_tarski('#skF_7'), B_89) | ~r2_hidden(C_88, '#skF_8'))), inference(resolution, [status(thm)], [c_237, c_2])).
% 3.02/1.48  tff(c_340, plain, (![C_97, A_98]: (r2_hidden(C_97, A_98) | ~r2_hidden(C_97, '#skF_8') | ~r1_setfam_1('#skF_7', k1_tarski(A_98)))), inference(resolution, [status(thm)], [c_164, c_267])).
% 3.02/1.48  tff(c_766, plain, (![B_177, A_178]: (r2_hidden('#skF_1'('#skF_8', B_177), A_178) | ~r1_setfam_1('#skF_7', k1_tarski(A_178)) | r1_tarski('#skF_8', B_177))), inference(resolution, [status(thm)], [c_6, c_340])).
% 3.02/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.48  tff(c_804, plain, (![A_179]: (~r1_setfam_1('#skF_7', k1_tarski(A_179)) | r1_tarski('#skF_8', A_179))), inference(resolution, [status(thm)], [c_766, c_4])).
% 3.02/1.48  tff(c_807, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_804])).
% 3.02/1.48  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_807])).
% 3.02/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  Inference rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Ref     : 0
% 3.02/1.48  #Sup     : 186
% 3.02/1.48  #Fact    : 0
% 3.02/1.48  #Define  : 0
% 3.02/1.48  #Split   : 6
% 3.02/1.48  #Chain   : 0
% 3.02/1.48  #Close   : 0
% 3.02/1.48  
% 3.02/1.48  Ordering : KBO
% 3.02/1.48  
% 3.02/1.48  Simplification rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Subsume      : 29
% 3.02/1.48  #Demod        : 17
% 3.02/1.48  #Tautology    : 29
% 3.02/1.48  #SimpNegUnit  : 1
% 3.02/1.48  #BackRed      : 1
% 3.02/1.48  
% 3.02/1.48  #Partial instantiations: 0
% 3.02/1.48  #Strategies tried      : 1
% 3.02/1.48  
% 3.02/1.48  Timing (in seconds)
% 3.02/1.48  ----------------------
% 3.02/1.48  Preprocessing        : 0.30
% 3.02/1.48  Parsing              : 0.15
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.39
% 3.02/1.48  Inferencing          : 0.14
% 3.02/1.48  Reduction            : 0.11
% 3.02/1.48  Demodulation         : 0.07
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.10
% 3.23/1.48  Abstraction          : 0.02
% 3.23/1.48  MUC search           : 0.00
% 3.23/1.48  Cooper               : 0.00
% 3.23/1.48  Total                : 0.72
% 3.23/1.48  Index Insertion      : 0.00
% 3.23/1.48  Index Deletion       : 0.00
% 3.23/1.48  Index Matching       : 0.00
% 3.23/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
