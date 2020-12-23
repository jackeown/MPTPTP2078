%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_257,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(A_70,B_69)
      | ~ v1_zfmisc_1(B_69)
      | v1_xboole_0(B_69)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_270,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = A_71
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | v1_xboole_0(k4_xboole_0(A_71,B_72)) ) ),
    inference(resolution,[status(thm)],[c_2,c_257])).

tff(c_279,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = A_3
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3)
      | v1_xboole_0(k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_336,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ v1_zfmisc_1(A_80)
      | v1_xboole_0(A_80)
      | v1_xboole_0(k3_xboole_0(A_80,B_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_279])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_339,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_26])).

tff(c_348,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_339])).

tff(c_349,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_348])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [B_48,A_49] : k1_setfam_1(k2_tarski(B_48,A_49)) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_20,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,A_55) = k3_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_20])).

tff(c_112,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_50,B_51] : r1_tarski(k3_xboole_0(A_50,B_51),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_146,plain,(
    ! [B_54,A_55] : r1_tarski(k3_xboole_0(B_54,A_55),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_121])).

tff(c_363,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_146])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:21:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.28  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1
% 2.21/1.28  
% 2.21/1.28  %Foreground sorts:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Background operators:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Foreground operators:
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.21/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.28  
% 2.21/1.29  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.21/1.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.21/1.29  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.21/1.29  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.21/1.29  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.21/1.29  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.21/1.29  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.29  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.29  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.29  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.29  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.29  tff(c_257, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(A_70, B_69) | ~v1_zfmisc_1(B_69) | v1_xboole_0(B_69) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.29  tff(c_270, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=A_71 | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | v1_xboole_0(k4_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_2, c_257])).
% 2.21/1.29  tff(c_279, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=A_3 | ~v1_zfmisc_1(A_3) | v1_xboole_0(A_3) | v1_xboole_0(k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 2.21/1.29  tff(c_336, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~v1_zfmisc_1(A_80) | v1_xboole_0(A_80) | v1_xboole_0(k3_xboole_0(A_80, B_81)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_279])).
% 2.21/1.29  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.29  tff(c_339, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_336, c_26])).
% 2.21/1.29  tff(c_348, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_339])).
% 2.21/1.29  tff(c_349, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_348])).
% 2.21/1.29  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.29  tff(c_65, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.29  tff(c_89, plain, (![B_48, A_49]: (k1_setfam_1(k2_tarski(B_48, A_49))=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 2.21/1.29  tff(c_20, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.29  tff(c_131, plain, (![B_54, A_55]: (k3_xboole_0(B_54, A_55)=k3_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_89, c_20])).
% 2.21/1.29  tff(c_112, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.29  tff(c_121, plain, (![A_50, B_51]: (r1_tarski(k3_xboole_0(A_50, B_51), A_50))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 2.21/1.29  tff(c_146, plain, (![B_54, A_55]: (r1_tarski(k3_xboole_0(B_54, A_55), A_55))), inference(superposition, [status(thm), theory('equality')], [c_131, c_121])).
% 2.21/1.29  tff(c_363, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_349, c_146])).
% 2.21/1.29  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_363])).
% 2.21/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  Inference rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Ref     : 0
% 2.21/1.29  #Sup     : 85
% 2.21/1.29  #Fact    : 0
% 2.21/1.29  #Define  : 0
% 2.21/1.29  #Split   : 0
% 2.21/1.29  #Chain   : 0
% 2.21/1.29  #Close   : 0
% 2.21/1.29  
% 2.21/1.29  Ordering : KBO
% 2.21/1.29  
% 2.21/1.29  Simplification rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Subsume      : 2
% 2.21/1.29  #Demod        : 24
% 2.21/1.29  #Tautology    : 55
% 2.21/1.29  #SimpNegUnit  : 3
% 2.21/1.29  #BackRed      : 1
% 2.21/1.29  
% 2.21/1.29  #Partial instantiations: 0
% 2.21/1.29  #Strategies tried      : 1
% 2.21/1.29  
% 2.21/1.29  Timing (in seconds)
% 2.21/1.29  ----------------------
% 2.21/1.30  Preprocessing        : 0.31
% 2.21/1.30  Parsing              : 0.16
% 2.21/1.30  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.23
% 2.21/1.30  Inferencing          : 0.09
% 2.21/1.30  Reduction            : 0.08
% 2.21/1.30  Demodulation         : 0.07
% 2.21/1.30  BG Simplification    : 0.02
% 2.21/1.30  Subsumption          : 0.03
% 2.21/1.30  Abstraction          : 0.02
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.57
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
