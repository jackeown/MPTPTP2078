%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 106 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 208 expanded)
%              Number of equality atoms :   19 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6,D_8] :
      ( r1_tarski(A_5,C_7)
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23,c_12])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_6,plain,(
    ! [A_2,B_3,C_4] :
      ( ~ r1_tarski(k2_zfmisc_1(A_2,B_3),k2_zfmisc_1(A_2,C_4))
      | r1_tarski(B_3,C_4)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [C_4] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_1',C_4))
      | r1_tarski('#skF_2',C_4)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_55,plain,(
    ! [C_4] :
      ( r1_tarski('#skF_2',C_4)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_65,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_65])).

tff(c_68,plain,(
    ! [C_4] : r1_tarski('#skF_2',C_4) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_75,plain,(
    ! [B_23,D_24,A_25,C_26] :
      ( r1_tarski(B_23,D_24)
      | k2_zfmisc_1(A_25,B_23) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_25,B_23),k2_zfmisc_1(C_26,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23,c_75])).

tff(c_81,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_78])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_81])).

tff(c_83,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_87,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_12])).

tff(c_90,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_87])).

tff(c_8,plain,(
    ! [B_3,A_2,C_4] :
      ( ~ r1_tarski(k2_zfmisc_1(B_3,A_2),k2_zfmisc_1(C_4,A_2))
      | r1_tarski(B_3,C_4)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [C_4] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_4,'#skF_1'))
      | r1_tarski('#skF_2',C_4)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_119,plain,(
    ! [C_4] :
      ( r1_tarski('#skF_2',C_4)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_108])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_146,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_146])).

tff(c_150,plain,(
    ! [C_4] : r1_tarski('#skF_2',C_4) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:09:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  %$ r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.61/1.15  
% 1.61/1.15  %Foreground sorts:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Background operators:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Foreground operators:
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.15  
% 1.61/1.16  tff(f_58, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.61/1.16  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.61/1.16  tff(f_47, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.61/1.16  tff(f_39, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 1.61/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.61/1.16  tff(c_18, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.61/1.16  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.61/1.16  tff(c_14, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.61/1.16  tff(c_16, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.61/1.16  tff(c_23, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_16])).
% 1.61/1.16  tff(c_12, plain, (![A_5, C_7, B_6, D_8]: (r1_tarski(A_5, C_7) | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.61/1.16  tff(c_27, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_23, c_12])).
% 1.61/1.16  tff(c_28, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_27])).
% 1.61/1.16  tff(c_6, plain, (![A_2, B_3, C_4]: (~r1_tarski(k2_zfmisc_1(A_2, B_3), k2_zfmisc_1(A_2, C_4)) | r1_tarski(B_3, C_4) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.16  tff(c_40, plain, (![C_4]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_1', C_4)) | r1_tarski('#skF_2', C_4) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_6])).
% 1.61/1.16  tff(c_55, plain, (![C_4]: (r1_tarski('#skF_2', C_4) | k1_xboole_0='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_40])).
% 1.61/1.16  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_55])).
% 1.61/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.61/1.16  tff(c_65, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 1.61/1.16  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_65])).
% 1.61/1.16  tff(c_68, plain, (![C_4]: (r1_tarski('#skF_2', C_4))), inference(splitRight, [status(thm)], [c_55])).
% 1.61/1.16  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_14])).
% 1.61/1.16  tff(c_74, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_27])).
% 1.61/1.16  tff(c_75, plain, (![B_23, D_24, A_25, C_26]: (r1_tarski(B_23, D_24) | k2_zfmisc_1(A_25, B_23)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_25, B_23), k2_zfmisc_1(C_26, D_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.61/1.16  tff(c_78, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_23, c_75])).
% 1.61/1.16  tff(c_81, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_78])).
% 1.61/1.16  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_81])).
% 1.61/1.16  tff(c_83, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_16])).
% 1.61/1.16  tff(c_87, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_83, c_12])).
% 1.61/1.16  tff(c_90, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_87])).
% 1.61/1.16  tff(c_8, plain, (![B_3, A_2, C_4]: (~r1_tarski(k2_zfmisc_1(B_3, A_2), k2_zfmisc_1(C_4, A_2)) | r1_tarski(B_3, C_4) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.16  tff(c_108, plain, (![C_4]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_4, '#skF_1')) | r1_tarski('#skF_2', C_4) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 1.61/1.16  tff(c_119, plain, (![C_4]: (r1_tarski('#skF_2', C_4) | k1_xboole_0='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_108])).
% 1.61/1.16  tff(c_138, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_119])).
% 1.61/1.16  tff(c_146, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2])).
% 1.61/1.16  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_146])).
% 1.61/1.16  tff(c_150, plain, (![C_4]: (r1_tarski('#skF_2', C_4))), inference(splitRight, [status(thm)], [c_119])).
% 1.61/1.16  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_14])).
% 1.61/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  Inference rules
% 1.61/1.16  ----------------------
% 1.61/1.16  #Ref     : 0
% 1.61/1.16  #Sup     : 21
% 1.61/1.16  #Fact    : 0
% 1.61/1.16  #Define  : 0
% 1.61/1.16  #Split   : 6
% 1.61/1.16  #Chain   : 0
% 1.61/1.16  #Close   : 0
% 1.61/1.16  
% 1.61/1.16  Ordering : KBO
% 1.61/1.16  
% 1.61/1.16  Simplification rules
% 1.61/1.16  ----------------------
% 1.61/1.16  #Subsume      : 0
% 1.61/1.16  #Demod        : 35
% 1.61/1.16  #Tautology    : 11
% 1.61/1.16  #SimpNegUnit  : 5
% 1.61/1.16  #BackRed      : 24
% 1.61/1.16  
% 1.61/1.16  #Partial instantiations: 0
% 1.61/1.16  #Strategies tried      : 1
% 1.61/1.16  
% 1.61/1.16  Timing (in seconds)
% 1.61/1.16  ----------------------
% 1.61/1.16  Preprocessing        : 0.25
% 1.61/1.16  Parsing              : 0.15
% 1.61/1.16  CNF conversion       : 0.02
% 1.61/1.16  Main loop            : 0.14
% 1.61/1.16  Inferencing          : 0.05
% 1.61/1.16  Reduction            : 0.04
% 1.61/1.16  Demodulation         : 0.03
% 1.61/1.16  BG Simplification    : 0.01
% 1.61/1.16  Subsumption          : 0.03
% 1.61/1.16  Abstraction          : 0.01
% 1.61/1.16  MUC search           : 0.00
% 1.61/1.16  Cooper               : 0.00
% 1.61/1.16  Total                : 0.42
% 1.61/1.16  Index Insertion      : 0.00
% 1.61/1.16  Index Deletion       : 0.00
% 1.61/1.16  Index Matching       : 0.00
% 1.61/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
