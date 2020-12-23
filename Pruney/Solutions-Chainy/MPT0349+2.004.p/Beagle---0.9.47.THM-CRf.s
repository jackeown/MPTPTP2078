%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:24 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   51 (  53 expanded)
%              Number of leaves         :   32 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [A_66,B_67] : k5_xboole_0(k5_xboole_0(A_66,B_67),k2_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_286,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,k1_xboole_0),A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_244])).

tff(c_386,plain,(
    ! [A_71] : k3_xboole_0(A_71,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_286])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_391,plain,(
    ! [A_71] : k5_xboole_0(A_71,k1_xboole_0) = k4_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_4])).

tff(c_395,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_391])).

tff(c_36,plain,(
    ! [A_46] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_510,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_513,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = k3_subset_1(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_510])).

tff(c_515,plain,(
    ! [A_46] : k3_subset_1(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_513])).

tff(c_30,plain,(
    ! [A_42] : k1_subset_1(A_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_40,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_39])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.13/1.30  
% 2.13/1.30  %Foreground sorts:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Background operators:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Foreground operators:
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.13/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.30  
% 2.42/1.31  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.42/1.31  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.42/1.31  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.42/1.31  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.42/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.42/1.31  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.42/1.31  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.42/1.31  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.42/1.31  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.42/1.31  tff(f_66, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.42/1.31  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.31  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.31  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.31  tff(c_244, plain, (![A_66, B_67]: (k5_xboole_0(k5_xboole_0(A_66, B_67), k2_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.31  tff(c_286, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, k1_xboole_0), A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_244])).
% 2.42/1.31  tff(c_386, plain, (![A_71]: (k3_xboole_0(A_71, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_286])).
% 2.42/1.31  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.31  tff(c_391, plain, (![A_71]: (k5_xboole_0(A_71, k1_xboole_0)=k4_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_386, c_4])).
% 2.42/1.31  tff(c_395, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_391])).
% 2.42/1.31  tff(c_36, plain, (![A_46]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.31  tff(c_510, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.31  tff(c_513, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=k3_subset_1(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_510])).
% 2.42/1.31  tff(c_515, plain, (![A_46]: (k3_subset_1(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_395, c_513])).
% 2.42/1.31  tff(c_30, plain, (![A_42]: (k1_subset_1(A_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.31  tff(c_32, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.42/1.31  tff(c_38, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.31  tff(c_39, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 2.42/1.31  tff(c_40, plain, (k3_subset_1('#skF_1', k1_xboole_0)!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_39])).
% 2.42/1.31  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_515, c_40])).
% 2.42/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  Inference rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Ref     : 0
% 2.42/1.31  #Sup     : 116
% 2.42/1.31  #Fact    : 0
% 2.42/1.31  #Define  : 0
% 2.42/1.31  #Split   : 0
% 2.42/1.31  #Chain   : 0
% 2.42/1.31  #Close   : 0
% 2.42/1.31  
% 2.42/1.31  Ordering : KBO
% 2.42/1.31  
% 2.42/1.31  Simplification rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Subsume      : 0
% 2.42/1.31  #Demod        : 43
% 2.42/1.31  #Tautology    : 75
% 2.42/1.31  #SimpNegUnit  : 0
% 2.42/1.31  #BackRed      : 1
% 2.42/1.32  
% 2.42/1.32  #Partial instantiations: 0
% 2.42/1.32  #Strategies tried      : 1
% 2.42/1.32  
% 2.42/1.32  Timing (in seconds)
% 2.42/1.32  ----------------------
% 2.42/1.32  Preprocessing        : 0.32
% 2.42/1.32  Parsing              : 0.17
% 2.42/1.32  CNF conversion       : 0.02
% 2.42/1.32  Main loop            : 0.23
% 2.42/1.32  Inferencing          : 0.08
% 2.42/1.32  Reduction            : 0.09
% 2.42/1.32  Demodulation         : 0.08
% 2.42/1.32  BG Simplification    : 0.02
% 2.42/1.32  Subsumption          : 0.03
% 2.42/1.32  Abstraction          : 0.02
% 2.42/1.32  MUC search           : 0.00
% 2.42/1.32  Cooper               : 0.00
% 2.42/1.32  Total                : 0.58
% 2.42/1.32  Index Insertion      : 0.00
% 2.42/1.32  Index Deletion       : 0.00
% 2.42/1.32  Index Matching       : 0.00
% 2.42/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
