%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  74 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( ~ r1_xboole_0(A_48,B_49)
      | r1_xboole_0(k2_zfmisc_1(A_48,C_50),k2_zfmisc_1(B_49,D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [A_58,C_59,B_60,D_61] :
      ( k4_xboole_0(k2_zfmisc_1(A_58,C_59),k2_zfmisc_1(B_60,D_61)) = k2_zfmisc_1(A_58,C_59)
      | ~ r1_xboole_0(A_58,B_60) ) ),
    inference(resolution,[status(thm)],[c_88,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [C_70,D_66,B_68,A_67,A_69] :
      ( r1_xboole_0(A_69,k2_zfmisc_1(B_68,D_66))
      | ~ r1_tarski(A_69,k2_zfmisc_1(A_67,C_70))
      | ~ r1_xboole_0(A_67,B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_198,plain,(
    ! [A_72,B_73,D_74] :
      ( r1_xboole_0(A_72,k2_zfmisc_1(B_73,D_74))
      | ~ r1_xboole_0(k1_relat_1(A_72),B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_209,plain,(
    ! [D_74] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_74))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_198])).

tff(c_215,plain,(
    ! [D_74] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_209])).

tff(c_75,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_71] :
      ( k2_xboole_0(A_71,k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))) = k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_xboole_0(A_6,B_7)
      | ~ r1_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_296,plain,(
    ! [A_83,A_84] :
      ( r1_xboole_0(A_83,A_84)
      | ~ r1_xboole_0(A_83,k2_zfmisc_1(k1_relat_1(A_84),k2_relat_1(A_84)))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_308,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_215,c_296])).

tff(c_329,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_308])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:18:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.25  
% 2.17/1.26  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.17/1.26  tff(f_65, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.17/1.26  tff(f_61, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.17/1.26  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.17/1.26  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.17/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.17/1.26  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.17/1.26  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.26  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.26  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.26  tff(c_26, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.26  tff(c_22, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.17/1.26  tff(c_88, plain, (![A_48, B_49, C_50, D_51]: (~r1_xboole_0(A_48, B_49) | r1_xboole_0(k2_zfmisc_1(A_48, C_50), k2_zfmisc_1(B_49, D_51)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.26  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.17/1.26  tff(c_129, plain, (![A_58, C_59, B_60, D_61]: (k4_xboole_0(k2_zfmisc_1(A_58, C_59), k2_zfmisc_1(B_60, D_61))=k2_zfmisc_1(A_58, C_59) | ~r1_xboole_0(A_58, B_60))), inference(resolution, [status(thm)], [c_88, c_14])).
% 2.17/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.26  tff(c_167, plain, (![C_70, D_66, B_68, A_67, A_69]: (r1_xboole_0(A_69, k2_zfmisc_1(B_68, D_66)) | ~r1_tarski(A_69, k2_zfmisc_1(A_67, C_70)) | ~r1_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.17/1.26  tff(c_198, plain, (![A_72, B_73, D_74]: (r1_xboole_0(A_72, k2_zfmisc_1(B_73, D_74)) | ~r1_xboole_0(k1_relat_1(A_72), B_73) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_22, c_167])).
% 2.17/1.26  tff(c_209, plain, (![D_74]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_74)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_198])).
% 2.17/1.26  tff(c_215, plain, (![D_74]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_74)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_209])).
% 2.17/1.26  tff(c_75, plain, (![A_36]: (r1_tarski(A_36, k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.17/1.26  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.26  tff(c_171, plain, (![A_71]: (k2_xboole_0(A_71, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)))=k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_75, c_6])).
% 2.17/1.26  tff(c_12, plain, (![A_6, B_7, C_8]: (r1_xboole_0(A_6, B_7) | ~r1_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.26  tff(c_296, plain, (![A_83, A_84]: (r1_xboole_0(A_83, A_84) | ~r1_xboole_0(A_83, k2_zfmisc_1(k1_relat_1(A_84), k2_relat_1(A_84))) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 2.17/1.26  tff(c_308, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_215, c_296])).
% 2.17/1.26  tff(c_329, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_308])).
% 2.17/1.26  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_329])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 70
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 0
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 2
% 2.17/1.26  #Demod        : 4
% 2.17/1.26  #Tautology    : 35
% 2.17/1.26  #SimpNegUnit  : 1
% 2.17/1.26  #BackRed      : 0
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.29
% 2.17/1.27  Parsing              : 0.17
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.23
% 2.17/1.27  Inferencing          : 0.10
% 2.17/1.27  Reduction            : 0.05
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.05
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.55
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
