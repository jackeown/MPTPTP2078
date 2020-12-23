%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   51 (  54 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  68 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    r1_setfam_1('#skF_7',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [B_7] : k2_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_18,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_83,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = k2_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_86,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_215,plain,(
    ! [C_75,A_76,D_77] :
      ( r2_hidden(C_75,k3_tarski(A_76))
      | ~ r2_hidden(D_77,A_76)
      | ~ r2_hidden(C_75,D_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_240,plain,(
    ! [C_80] :
      ( r2_hidden(C_80,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_80,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_215])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,k3_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_83,k3_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_240,c_4])).

tff(c_290,plain,(
    r1_tarski('#skF_8',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k3_tarski(A_37),k3_tarski(B_38))
      | ~ r1_setfam_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_751,plain,(
    ! [A_128,B_129,A_130] :
      ( r1_tarski(A_128,k3_tarski(B_129))
      | ~ r1_tarski(A_128,k3_tarski(A_130))
      | ~ r1_setfam_1(A_130,B_129) ) ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_779,plain,(
    ! [B_131] :
      ( r1_tarski('#skF_8',k3_tarski(B_131))
      | ~ r1_setfam_1('#skF_7',B_131) ) ),
    inference(resolution,[status(thm)],[c_290,c_751])).

tff(c_806,plain,(
    ! [A_132] :
      ( r1_tarski('#skF_8',A_132)
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_779])).

tff(c_809,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_806])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.70/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.70/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.70/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.70/1.43  
% 2.70/1.44  tff(f_76, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.70/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.44  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.70/1.44  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.44  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.70/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.70/1.44  tff(f_62, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.70/1.44  tff(f_68, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.70/1.44  tff(f_48, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.70/1.44  tff(c_44, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.70/1.44  tff(c_48, plain, (r1_setfam_1('#skF_7', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.70/1.44  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.44  tff(c_60, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.70/1.44  tff(c_64, plain, (![B_7]: (k2_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_60])).
% 2.70/1.44  tff(c_18, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.44  tff(c_74, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.44  tff(c_83, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=k2_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_74])).
% 2.70/1.44  tff(c_86, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_83])).
% 2.70/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.44  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.70/1.44  tff(c_215, plain, (![C_75, A_76, D_77]: (r2_hidden(C_75, k3_tarski(A_76)) | ~r2_hidden(D_77, A_76) | ~r2_hidden(C_75, D_77))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.44  tff(c_240, plain, (![C_80]: (r2_hidden(C_80, k3_tarski('#skF_7')) | ~r2_hidden(C_80, '#skF_8'))), inference(resolution, [status(thm)], [c_46, c_215])).
% 2.70/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.44  tff(c_285, plain, (![A_83]: (r1_tarski(A_83, k3_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_83, k3_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_240, c_4])).
% 2.70/1.44  tff(c_290, plain, (r1_tarski('#skF_8', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_285])).
% 2.70/1.44  tff(c_42, plain, (![A_37, B_38]: (r1_tarski(k3_tarski(A_37), k3_tarski(B_38)) | ~r1_setfam_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.44  tff(c_154, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.44  tff(c_751, plain, (![A_128, B_129, A_130]: (r1_tarski(A_128, k3_tarski(B_129)) | ~r1_tarski(A_128, k3_tarski(A_130)) | ~r1_setfam_1(A_130, B_129))), inference(resolution, [status(thm)], [c_42, c_154])).
% 2.70/1.44  tff(c_779, plain, (![B_131]: (r1_tarski('#skF_8', k3_tarski(B_131)) | ~r1_setfam_1('#skF_7', B_131))), inference(resolution, [status(thm)], [c_290, c_751])).
% 2.70/1.44  tff(c_806, plain, (![A_132]: (r1_tarski('#skF_8', A_132) | ~r1_setfam_1('#skF_7', k1_tarski(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_779])).
% 2.70/1.44  tff(c_809, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_806])).
% 2.70/1.44  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_809])).
% 2.70/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.44  
% 2.70/1.44  Inference rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Ref     : 0
% 2.70/1.44  #Sup     : 196
% 2.70/1.44  #Fact    : 0
% 2.70/1.44  #Define  : 0
% 2.70/1.44  #Split   : 6
% 2.70/1.44  #Chain   : 0
% 2.70/1.44  #Close   : 0
% 2.70/1.44  
% 2.70/1.44  Ordering : KBO
% 2.70/1.44  
% 2.70/1.44  Simplification rules
% 2.70/1.44  ----------------------
% 3.02/1.44  #Subsume      : 23
% 3.02/1.44  #Demod        : 16
% 3.02/1.44  #Tautology    : 29
% 3.02/1.44  #SimpNegUnit  : 1
% 3.02/1.44  #BackRed      : 0
% 3.02/1.44  
% 3.02/1.44  #Partial instantiations: 0
% 3.02/1.44  #Strategies tried      : 1
% 3.02/1.44  
% 3.02/1.44  Timing (in seconds)
% 3.02/1.44  ----------------------
% 3.02/1.44  Preprocessing        : 0.31
% 3.02/1.44  Parsing              : 0.16
% 3.02/1.44  CNF conversion       : 0.02
% 3.02/1.44  Main loop            : 0.38
% 3.02/1.44  Inferencing          : 0.13
% 3.02/1.44  Reduction            : 0.11
% 3.02/1.44  Demodulation         : 0.07
% 3.02/1.44  BG Simplification    : 0.02
% 3.02/1.44  Subsumption          : 0.09
% 3.02/1.44  Abstraction          : 0.02
% 3.02/1.44  MUC search           : 0.00
% 3.02/1.44  Cooper               : 0.00
% 3.02/1.44  Total                : 0.71
% 3.02/1.44  Index Insertion      : 0.00
% 3.02/1.44  Index Deletion       : 0.00
% 3.02/1.44  Index Matching       : 0.00
% 3.02/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
