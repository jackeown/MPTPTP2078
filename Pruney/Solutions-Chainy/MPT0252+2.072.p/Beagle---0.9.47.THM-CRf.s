%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:09 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  84 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [B_64,A_63] : r2_hidden(B_64,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_16])).

tff(c_65,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k3_tarski(B_46))
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_752,plain,(
    ! [A_172,A_173,B_174] :
      ( r1_tarski(A_172,k2_xboole_0(A_173,B_174))
      | ~ r2_hidden(A_172,k2_tarski(A_173,B_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_52])).

tff(c_765,plain,(
    ! [B_64,A_63] : r1_tarski(B_64,k2_xboole_0(A_63,B_64)) ),
    inference(resolution,[status(thm)],[c_83,c_752])).

tff(c_58,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_229,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_236,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_229])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_375])).

tff(c_800,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_54,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_18])).

tff(c_251,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_270,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden(A_86,B_87)
      | ~ r1_tarski(k2_tarski(A_86,B_88),B_87) ) ),
    inference(resolution,[status(thm)],[c_86,c_251])).

tff(c_921,plain,(
    ! [A_202,B_203,B_204] :
      ( r2_hidden(A_202,k3_tarski(B_203))
      | ~ r2_hidden(k2_tarski(A_202,B_204),B_203) ) ),
    inference(resolution,[status(thm)],[c_52,c_270])).

tff(c_933,plain,(
    ! [A_202,B_204,B_64] : r2_hidden(A_202,k3_tarski(k2_tarski(k2_tarski(A_202,B_204),B_64))) ),
    inference(resolution,[status(thm)],[c_86,c_921])).

tff(c_959,plain,(
    ! [A_205,B_206,B_207] : r2_hidden(A_205,k2_xboole_0(k2_tarski(A_205,B_206),B_207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_933])).

tff(c_972,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_959])).

tff(c_977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.55  
% 2.74/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.56  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.74/1.56  
% 2.74/1.56  %Foreground sorts:
% 2.74/1.56  
% 2.74/1.56  
% 2.74/1.56  %Background operators:
% 2.74/1.56  
% 2.74/1.56  
% 2.74/1.56  %Foreground operators:
% 2.74/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.56  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.74/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.56  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.74/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.56  
% 2.74/1.57  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.74/1.57  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.74/1.57  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.74/1.57  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.74/1.57  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.74/1.57  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.57  tff(c_56, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.57  tff(c_77, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.57  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.57  tff(c_83, plain, (![B_64, A_63]: (r2_hidden(B_64, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_16])).
% 2.74/1.57  tff(c_65, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.74/1.57  tff(c_52, plain, (![A_45, B_46]: (r1_tarski(A_45, k3_tarski(B_46)) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.57  tff(c_752, plain, (![A_172, A_173, B_174]: (r1_tarski(A_172, k2_xboole_0(A_173, B_174)) | ~r2_hidden(A_172, k2_tarski(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_52])).
% 2.74/1.57  tff(c_765, plain, (![B_64, A_63]: (r1_tarski(B_64, k2_xboole_0(A_63, B_64)))), inference(resolution, [status(thm)], [c_83, c_752])).
% 2.74/1.57  tff(c_58, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.57  tff(c_229, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.57  tff(c_236, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_229])).
% 2.74/1.57  tff(c_375, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_236])).
% 2.74/1.57  tff(c_799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_765, c_375])).
% 2.74/1.57  tff(c_800, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_236])).
% 2.74/1.57  tff(c_54, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.74/1.57  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.57  tff(c_86, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_18])).
% 2.74/1.57  tff(c_251, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.57  tff(c_270, plain, (![A_86, B_87, B_88]: (r2_hidden(A_86, B_87) | ~r1_tarski(k2_tarski(A_86, B_88), B_87))), inference(resolution, [status(thm)], [c_86, c_251])).
% 2.74/1.57  tff(c_921, plain, (![A_202, B_203, B_204]: (r2_hidden(A_202, k3_tarski(B_203)) | ~r2_hidden(k2_tarski(A_202, B_204), B_203))), inference(resolution, [status(thm)], [c_52, c_270])).
% 2.74/1.57  tff(c_933, plain, (![A_202, B_204, B_64]: (r2_hidden(A_202, k3_tarski(k2_tarski(k2_tarski(A_202, B_204), B_64))))), inference(resolution, [status(thm)], [c_86, c_921])).
% 2.74/1.57  tff(c_959, plain, (![A_205, B_206, B_207]: (r2_hidden(A_205, k2_xboole_0(k2_tarski(A_205, B_206), B_207)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_933])).
% 2.74/1.57  tff(c_972, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_800, c_959])).
% 2.74/1.57  tff(c_977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_972])).
% 2.74/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.57  
% 2.74/1.57  Inference rules
% 2.74/1.57  ----------------------
% 2.74/1.57  #Ref     : 0
% 2.74/1.57  #Sup     : 198
% 2.74/1.57  #Fact    : 0
% 2.74/1.57  #Define  : 0
% 2.74/1.57  #Split   : 1
% 2.74/1.57  #Chain   : 0
% 2.74/1.57  #Close   : 0
% 2.74/1.57  
% 2.74/1.57  Ordering : KBO
% 2.74/1.57  
% 2.74/1.57  Simplification rules
% 2.74/1.57  ----------------------
% 2.74/1.57  #Subsume      : 13
% 2.74/1.57  #Demod        : 76
% 2.74/1.57  #Tautology    : 91
% 2.74/1.57  #SimpNegUnit  : 1
% 2.74/1.57  #BackRed      : 2
% 2.74/1.57  
% 2.74/1.57  #Partial instantiations: 0
% 2.74/1.57  #Strategies tried      : 1
% 2.74/1.57  
% 2.74/1.57  Timing (in seconds)
% 2.74/1.57  ----------------------
% 2.74/1.57  Preprocessing        : 0.32
% 2.74/1.57  Parsing              : 0.16
% 2.74/1.57  CNF conversion       : 0.02
% 2.74/1.57  Main loop            : 0.34
% 2.74/1.57  Inferencing          : 0.12
% 2.74/1.57  Reduction            : 0.11
% 2.74/1.57  Demodulation         : 0.09
% 2.74/1.57  BG Simplification    : 0.02
% 2.74/1.57  Subsumption          : 0.07
% 2.74/1.57  Abstraction          : 0.02
% 2.74/1.57  MUC search           : 0.00
% 2.74/1.57  Cooper               : 0.00
% 2.74/1.57  Total                : 0.68
% 2.74/1.57  Index Insertion      : 0.00
% 2.74/1.57  Index Deletion       : 0.00
% 2.74/1.57  Index Matching       : 0.00
% 2.74/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
