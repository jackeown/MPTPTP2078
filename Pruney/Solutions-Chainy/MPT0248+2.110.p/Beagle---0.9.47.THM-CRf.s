%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 117 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 288 expanded)
%              Number of equality atoms :   54 ( 240 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_185,plain,(
    ! [B_40,A_41] :
      ( k1_tarski(B_40) = A_41
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_tarski(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_195,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_55,c_185])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_46,c_195])).

tff(c_207,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,k2_xboole_0(C_51,B_52))
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_50,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_276])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_345,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(B_62) = A_63
      | A_63 = '#skF_2'
      | ~ r1_tarski(A_63,k1_tarski(B_62)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_18])).

tff(c_362,plain,(
    ! [A_64] :
      ( k1_tarski('#skF_1') = A_64
      | A_64 = '#skF_2'
      | ~ r1_tarski(A_64,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_285,c_345])).

tff(c_370,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_362])).

tff(c_377,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_370])).

tff(c_10,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_10])).

tff(c_383,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_3') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_209])).

tff(c_385,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_32])).

tff(c_439,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_385])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_439])).

tff(c_441,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_442,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_475,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_442,c_30])).

tff(c_465,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_32])).

tff(c_536,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,k2_xboole_0(C_79,B_80))
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_545,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,'#skF_2')
      | ~ r1_tarski(A_78,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_536])).

tff(c_616,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_623,plain,(
    ! [A_92] :
      ( k1_tarski('#skF_1') = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_616])).

tff(c_633,plain,(
    ! [A_93] :
      ( A_93 = '#skF_2'
      | k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_623])).

tff(c_654,plain,(
    ! [A_94] :
      ( A_94 = '#skF_2'
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_545,c_633])).

tff(c_662,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_654])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_475,c_662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.31  
% 2.31/1.31  %Foreground sorts:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Background operators:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Foreground operators:
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.31  
% 2.31/1.33  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.31/1.33  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.31/1.33  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.31/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.33  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.31/1.33  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.31/1.33  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.33  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.31/1.33  tff(c_26, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.33  tff(c_46, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.31/1.33  tff(c_32, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.33  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.33  tff(c_55, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_12])).
% 2.31/1.33  tff(c_185, plain, (![B_40, A_41]: (k1_tarski(B_40)=A_41 | k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.33  tff(c_195, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_55, c_185])).
% 2.31/1.33  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_46, c_195])).
% 2.31/1.33  tff(c_207, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.31/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.33  tff(c_276, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, k2_xboole_0(C_51, B_52)) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.33  tff(c_285, plain, (![A_50]: (r1_tarski(A_50, k1_tarski('#skF_1')) | ~r1_tarski(A_50, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_276])).
% 2.31/1.33  tff(c_208, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.31/1.33  tff(c_18, plain, (![B_13, A_12]: (k1_tarski(B_13)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.33  tff(c_345, plain, (![B_62, A_63]: (k1_tarski(B_62)=A_63 | A_63='#skF_2' | ~r1_tarski(A_63, k1_tarski(B_62)))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_18])).
% 2.31/1.33  tff(c_362, plain, (![A_64]: (k1_tarski('#skF_1')=A_64 | A_64='#skF_2' | ~r1_tarski(A_64, '#skF_3'))), inference(resolution, [status(thm)], [c_285, c_345])).
% 2.31/1.33  tff(c_370, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6, c_362])).
% 2.31/1.33  tff(c_377, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_207, c_370])).
% 2.31/1.33  tff(c_10, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.33  tff(c_209, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_10])).
% 2.31/1.33  tff(c_383, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_3')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_377, c_209])).
% 2.31/1.33  tff(c_385, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_32])).
% 2.31/1.33  tff(c_439, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_385])).
% 2.31/1.33  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_439])).
% 2.31/1.33  tff(c_441, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.31/1.33  tff(c_442, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.31/1.33  tff(c_30, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.33  tff(c_475, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_442, c_30])).
% 2.31/1.33  tff(c_465, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_32])).
% 2.31/1.33  tff(c_536, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, k2_xboole_0(C_79, B_80)) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.33  tff(c_545, plain, (![A_78]: (r1_tarski(A_78, '#skF_2') | ~r1_tarski(A_78, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_465, c_536])).
% 2.31/1.33  tff(c_616, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.33  tff(c_623, plain, (![A_92]: (k1_tarski('#skF_1')=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_616])).
% 2.31/1.33  tff(c_633, plain, (![A_93]: (A_93='#skF_2' | k1_xboole_0=A_93 | ~r1_tarski(A_93, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_623])).
% 2.31/1.33  tff(c_654, plain, (![A_94]: (A_94='#skF_2' | k1_xboole_0=A_94 | ~r1_tarski(A_94, '#skF_3'))), inference(resolution, [status(thm)], [c_545, c_633])).
% 2.31/1.33  tff(c_662, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_654])).
% 2.31/1.33  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_475, c_662])).
% 2.31/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  Inference rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Ref     : 0
% 2.31/1.33  #Sup     : 142
% 2.31/1.33  #Fact    : 0
% 2.31/1.33  #Define  : 0
% 2.31/1.33  #Split   : 4
% 2.31/1.33  #Chain   : 0
% 2.31/1.33  #Close   : 0
% 2.31/1.33  
% 2.31/1.33  Ordering : KBO
% 2.31/1.33  
% 2.31/1.33  Simplification rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Subsume      : 8
% 2.31/1.33  #Demod        : 43
% 2.31/1.33  #Tautology    : 86
% 2.31/1.33  #SimpNegUnit  : 9
% 2.31/1.33  #BackRed      : 11
% 2.31/1.33  
% 2.31/1.33  #Partial instantiations: 0
% 2.31/1.33  #Strategies tried      : 1
% 2.31/1.33  
% 2.31/1.33  Timing (in seconds)
% 2.31/1.33  ----------------------
% 2.31/1.33  Preprocessing        : 0.28
% 2.31/1.33  Parsing              : 0.15
% 2.31/1.33  CNF conversion       : 0.02
% 2.31/1.33  Main loop            : 0.27
% 2.31/1.33  Inferencing          : 0.10
% 2.31/1.33  Reduction            : 0.08
% 2.31/1.33  Demodulation         : 0.06
% 2.31/1.33  BG Simplification    : 0.01
% 2.31/1.33  Subsumption          : 0.05
% 2.31/1.33  Abstraction          : 0.01
% 2.31/1.33  MUC search           : 0.00
% 2.31/1.33  Cooper               : 0.00
% 2.31/1.33  Total                : 0.58
% 2.31/1.33  Index Insertion      : 0.00
% 2.31/1.33  Index Deletion       : 0.00
% 2.31/1.33  Index Matching       : 0.00
% 2.31/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
