%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 165 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 335 expanded)
%              Number of equality atoms :   37 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_84,plain,(
    ! [A_22,C_23,B_24,D_25] :
      ( r1_tarski(A_22,C_23)
      | k2_zfmisc_1(A_22,B_24) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_22,B_24),k2_zfmisc_1(C_23,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_107,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_176,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_176])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_191,plain,(
    ! [A_3] : k4_xboole_0('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_8])).

tff(c_54,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_187,plain,(
    k4_xboole_0('#skF_2','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_58])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_187])).

tff(c_243,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_252,plain,(
    ! [B_34,D_35,A_36,C_37] :
      ( r1_tarski(B_34,D_35)
      | k2_zfmisc_1(A_36,B_34) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_36,B_34),k2_zfmisc_1(C_37,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_255,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_252])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_20,c_255])).

tff(c_275,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_300,plain,(
    ! [B_40,D_41,A_42,C_43] :
      ( r1_tarski(B_40,D_41)
      | k2_zfmisc_1(A_42,B_40) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_42,B_40),k2_zfmisc_1(C_43,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_319,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_300])).

tff(c_323,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_340,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_10])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_379,plain,(
    ! [A_3] : k4_xboole_0('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_8])).

tff(c_375,plain,(
    k4_xboole_0('#skF_2','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_58])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_375])).

tff(c_396,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_409,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_2])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_409])).

tff(c_413,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_418,plain,(
    ! [A_49,C_50,B_51,D_52] :
      ( r1_tarski(A_49,C_50)
      | k2_zfmisc_1(A_49,B_51) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_49,B_51),k2_zfmisc_1(C_50,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_421,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_418])).

tff(c_439,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_421])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  %$ r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.27  
% 2.09/1.29  tff(f_57, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.09/1.29  tff(f_46, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.09/1.29  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.29  tff(f_32, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.09/1.29  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.09/1.29  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.29  tff(c_22, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.29  tff(c_64, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.09/1.29  tff(c_84, plain, (![A_22, C_23, B_24, D_25]: (r1_tarski(A_22, C_23) | k2_zfmisc_1(A_22, B_24)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_22, B_24), k2_zfmisc_1(C_23, D_25)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.29  tff(c_103, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_84])).
% 2.09/1.29  tff(c_107, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_103])).
% 2.09/1.29  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.29  tff(c_156, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 2.09/1.29  tff(c_159, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_156])).
% 2.09/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.09/1.29  tff(c_176, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2])).
% 2.09/1.29  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_176])).
% 2.09/1.29  tff(c_179, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_156])).
% 2.09/1.29  tff(c_8, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.29  tff(c_191, plain, (![A_3]: (k4_xboole_0('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_8])).
% 2.09/1.29  tff(c_54, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.09/1.29  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.29  tff(c_58, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_20])).
% 2.09/1.29  tff(c_187, plain, (k4_xboole_0('#skF_2', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_58])).
% 2.09/1.29  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_187])).
% 2.09/1.29  tff(c_243, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_103])).
% 2.09/1.29  tff(c_252, plain, (![B_34, D_35, A_36, C_37]: (r1_tarski(B_34, D_35) | k2_zfmisc_1(A_36, B_34)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_36, B_34), k2_zfmisc_1(C_37, D_35)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.29  tff(c_255, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_252])).
% 2.09/1.29  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_20, c_255])).
% 2.09/1.29  tff(c_275, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 2.09/1.29  tff(c_300, plain, (![B_40, D_41, A_42, C_43]: (r1_tarski(B_40, D_41) | k2_zfmisc_1(A_42, B_40)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_42, B_40), k2_zfmisc_1(C_43, D_41)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.29  tff(c_319, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_300])).
% 2.09/1.29  tff(c_323, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_319])).
% 2.09/1.29  tff(c_340, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_323, c_10])).
% 2.09/1.29  tff(c_342, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_340])).
% 2.09/1.29  tff(c_379, plain, (![A_3]: (k4_xboole_0('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_8])).
% 2.09/1.29  tff(c_375, plain, (k4_xboole_0('#skF_2', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_58])).
% 2.09/1.29  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_375])).
% 2.09/1.29  tff(c_396, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_340])).
% 2.09/1.29  tff(c_409, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_2])).
% 2.09/1.29  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_409])).
% 2.09/1.29  tff(c_413, plain, (k2_zfmisc_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_319])).
% 2.09/1.29  tff(c_418, plain, (![A_49, C_50, B_51, D_52]: (r1_tarski(A_49, C_50) | k2_zfmisc_1(A_49, B_51)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_49, B_51), k2_zfmisc_1(C_50, D_52)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.29  tff(c_421, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_418])).
% 2.09/1.29  tff(c_439, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_421])).
% 2.09/1.29  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_439])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 92
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 5
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 0
% 2.09/1.29  #Demod        : 100
% 2.09/1.29  #Tautology    : 59
% 2.09/1.29  #SimpNegUnit  : 6
% 2.09/1.29  #BackRed      : 54
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.30  Preprocessing        : 0.27
% 2.09/1.30  Parsing              : 0.15
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.26
% 2.09/1.30  Inferencing          : 0.08
% 2.09/1.30  Reduction            : 0.09
% 2.09/1.30  Demodulation         : 0.06
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.05
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.58
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
