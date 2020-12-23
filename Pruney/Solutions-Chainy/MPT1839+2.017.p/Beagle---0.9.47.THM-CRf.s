%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  78 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_152,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | k4_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_160,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_48])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_300,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_315,plain,(
    ! [A_68,B_69] : k4_xboole_0(k3_xboole_0(A_68,B_69),A_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_71])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_495,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(A_80,B_79)
      | ~ v1_zfmisc_1(B_79)
      | v1_xboole_0(B_79)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4044,plain,(
    ! [B_226,A_227] :
      ( B_226 = A_227
      | ~ v1_zfmisc_1(B_226)
      | v1_xboole_0(B_226)
      | v1_xboole_0(A_227)
      | k4_xboole_0(A_227,B_226) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_495])).

tff(c_4046,plain,(
    ! [A_227] :
      ( A_227 = '#skF_4'
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_227)
      | k4_xboole_0(A_227,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_4044])).

tff(c_4176,plain,(
    ! [A_230] :
      ( A_230 = '#skF_4'
      | v1_xboole_0(A_230)
      | k4_xboole_0(A_230,'#skF_4') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4046])).

tff(c_50,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4201,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k4_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4176,c_50])).

tff(c_4217,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_4201])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4266,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4217,c_36])).

tff(c_4286,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4266])).

tff(c_4288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.87  
% 4.61/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.87  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 4.61/1.87  
% 4.61/1.87  %Foreground sorts:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Background operators:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Foreground operators:
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.61/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.61/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.87  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.61/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.61/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.61/1.87  
% 4.61/1.88  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.61/1.88  tff(f_88, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 4.61/1.88  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.61/1.88  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.61/1.88  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.61/1.88  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.61/1.88  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.61/1.88  tff(c_152, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | k4_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.88  tff(c_48, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.88  tff(c_160, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_48])).
% 4.61/1.88  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.61/1.88  tff(c_64, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.88  tff(c_72, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_64])).
% 4.61/1.88  tff(c_300, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.61/1.88  tff(c_34, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.61/1.88  tff(c_71, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_64])).
% 4.61/1.88  tff(c_315, plain, (![A_68, B_69]: (k4_xboole_0(k3_xboole_0(A_68, B_69), A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_300, c_71])).
% 4.61/1.88  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.88  tff(c_52, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.88  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.88  tff(c_495, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(A_80, B_79) | ~v1_zfmisc_1(B_79) | v1_xboole_0(B_79) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.61/1.88  tff(c_4044, plain, (![B_226, A_227]: (B_226=A_227 | ~v1_zfmisc_1(B_226) | v1_xboole_0(B_226) | v1_xboole_0(A_227) | k4_xboole_0(A_227, B_226)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_495])).
% 4.61/1.88  tff(c_4046, plain, (![A_227]: (A_227='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(A_227) | k4_xboole_0(A_227, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_4044])).
% 4.61/1.88  tff(c_4176, plain, (![A_230]: (A_230='#skF_4' | v1_xboole_0(A_230) | k4_xboole_0(A_230, '#skF_4')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_4046])).
% 4.61/1.88  tff(c_50, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.88  tff(c_4201, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | k4_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4176, c_50])).
% 4.61/1.88  tff(c_4217, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_4201])).
% 4.61/1.88  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.61/1.88  tff(c_4266, plain, (k4_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4217, c_36])).
% 4.61/1.88  tff(c_4286, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4266])).
% 4.61/1.88  tff(c_4288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_4286])).
% 4.61/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.88  
% 4.61/1.88  Inference rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Ref     : 0
% 4.61/1.88  #Sup     : 1042
% 4.61/1.88  #Fact    : 0
% 4.61/1.88  #Define  : 0
% 4.61/1.88  #Split   : 2
% 4.61/1.88  #Chain   : 0
% 4.61/1.88  #Close   : 0
% 4.61/1.88  
% 4.61/1.88  Ordering : KBO
% 4.61/1.88  
% 4.61/1.88  Simplification rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Subsume      : 305
% 4.61/1.88  #Demod        : 547
% 4.61/1.88  #Tautology    : 485
% 4.61/1.88  #SimpNegUnit  : 5
% 4.61/1.88  #BackRed      : 8
% 4.61/1.88  
% 4.61/1.88  #Partial instantiations: 0
% 4.61/1.88  #Strategies tried      : 1
% 4.61/1.88  
% 4.61/1.88  Timing (in seconds)
% 4.61/1.88  ----------------------
% 4.61/1.88  Preprocessing        : 0.33
% 4.61/1.88  Parsing              : 0.17
% 4.61/1.88  CNF conversion       : 0.02
% 4.61/1.88  Main loop            : 0.79
% 4.61/1.88  Inferencing          : 0.28
% 4.61/1.88  Reduction            : 0.26
% 4.61/1.88  Demodulation         : 0.19
% 4.61/1.89  BG Simplification    : 0.03
% 4.61/1.89  Subsumption          : 0.17
% 4.61/1.89  Abstraction          : 0.05
% 4.61/1.89  MUC search           : 0.00
% 4.61/1.89  Cooper               : 0.00
% 4.61/1.89  Total                : 1.14
% 4.61/1.89  Index Insertion      : 0.00
% 4.61/1.89  Index Deletion       : 0.00
% 4.61/1.89  Index Matching       : 0.00
% 4.61/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
