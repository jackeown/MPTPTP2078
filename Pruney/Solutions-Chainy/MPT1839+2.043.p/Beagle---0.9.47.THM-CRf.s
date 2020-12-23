%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   47 (  50 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  70 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_44,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_24])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [B_40,A_41] :
      ( ~ r1_xboole_0(B_40,A_41)
      | ~ r1_tarski(B_40,A_41)
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_349,plain,(
    ! [A_59,B_60] :
      ( ~ r1_tarski(k4_xboole_0(A_59,B_60),B_60)
      | v1_xboole_0(k4_xboole_0(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_397,plain,(
    ! [A_63] : v1_xboole_0(k4_xboole_0(A_63,A_63)) ),
    inference(resolution,[status(thm)],[c_10,c_349])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_404,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_397,c_2])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(A_51,B_50)
      | ~ v1_zfmisc_1(B_50)
      | v1_xboole_0(B_50)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_565,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | v1_xboole_0(k3_xboole_0(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_571,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_565,c_26])).

tff(c_575,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_571])).

tff(c_576,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_575])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_605,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_12])).

tff(c_617,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_605])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.32  %$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.32  
% 1.97/1.32  %Foreground sorts:
% 1.97/1.32  
% 1.97/1.32  
% 1.97/1.32  %Background operators:
% 1.97/1.32  
% 1.97/1.32  
% 1.97/1.32  %Foreground operators:
% 1.97/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.97/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.32  
% 2.40/1.33  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.40/1.33  tff(f_78, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.40/1.33  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.40/1.33  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.40/1.33  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.40/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.33  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.40/1.33  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.40/1.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.40/1.33  tff(c_44, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.33  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.33  tff(c_48, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_24])).
% 2.40/1.33  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.33  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.33  tff(c_91, plain, (![B_40, A_41]: (~r1_xboole_0(B_40, A_41) | ~r1_tarski(B_40, A_41) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.33  tff(c_349, plain, (![A_59, B_60]: (~r1_tarski(k4_xboole_0(A_59, B_60), B_60) | v1_xboole_0(k4_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_16, c_91])).
% 2.40/1.33  tff(c_397, plain, (![A_63]: (v1_xboole_0(k4_xboole_0(A_63, A_63)))), inference(resolution, [status(thm)], [c_10, c_349])).
% 2.40/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.33  tff(c_404, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_397, c_2])).
% 2.40/1.33  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.33  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.33  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.33  tff(c_188, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(A_51, B_50) | ~v1_zfmisc_1(B_50) | v1_xboole_0(B_50) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.33  tff(c_565, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | v1_xboole_0(k3_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_8, c_188])).
% 2.40/1.33  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.33  tff(c_571, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_565, c_26])).
% 2.40/1.33  tff(c_575, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_571])).
% 2.40/1.33  tff(c_576, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_575])).
% 2.40/1.33  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.33  tff(c_605, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_576, c_12])).
% 2.40/1.33  tff(c_617, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_404, c_605])).
% 2.40/1.33  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_617])).
% 2.40/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.33  
% 2.40/1.33  Inference rules
% 2.40/1.33  ----------------------
% 2.40/1.33  #Ref     : 0
% 2.40/1.33  #Sup     : 142
% 2.40/1.33  #Fact    : 0
% 2.40/1.33  #Define  : 0
% 2.40/1.33  #Split   : 1
% 2.40/1.33  #Chain   : 0
% 2.40/1.33  #Close   : 0
% 2.40/1.33  
% 2.40/1.33  Ordering : KBO
% 2.40/1.33  
% 2.40/1.33  Simplification rules
% 2.40/1.33  ----------------------
% 2.40/1.33  #Subsume      : 3
% 2.40/1.33  #Demod        : 117
% 2.40/1.33  #Tautology    : 106
% 2.40/1.33  #SimpNegUnit  : 6
% 2.40/1.33  #BackRed      : 4
% 2.40/1.33  
% 2.40/1.33  #Partial instantiations: 0
% 2.40/1.33  #Strategies tried      : 1
% 2.40/1.33  
% 2.40/1.33  Timing (in seconds)
% 2.40/1.33  ----------------------
% 2.40/1.33  Preprocessing        : 0.28
% 2.40/1.33  Parsing              : 0.15
% 2.40/1.33  CNF conversion       : 0.02
% 2.40/1.33  Main loop            : 0.25
% 2.40/1.33  Inferencing          : 0.10
% 2.40/1.33  Reduction            : 0.08
% 2.40/1.33  Demodulation         : 0.06
% 2.40/1.33  BG Simplification    : 0.01
% 2.40/1.33  Subsumption          : 0.04
% 2.40/1.33  Abstraction          : 0.02
% 2.40/1.33  MUC search           : 0.00
% 2.40/1.33  Cooper               : 0.00
% 2.40/1.33  Total                : 0.55
% 2.40/1.33  Index Insertion      : 0.00
% 2.40/1.33  Index Deletion       : 0.00
% 2.40/1.33  Index Matching       : 0.00
% 2.40/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
