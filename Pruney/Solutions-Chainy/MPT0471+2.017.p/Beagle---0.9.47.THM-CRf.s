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
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  91 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  94 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_46,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_32,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    k3_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_32])).

tff(c_46,plain,(
    ! [A_29] :
      ( v1_relat_1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_124,plain,(
    ! [A_37] : k3_tarski(k1_tarski(A_37)) = k2_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_20,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    k1_zfmisc_1('#skF_1') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_20])).

tff(c_72,plain,(
    ! [A_30] : k3_tarski(k1_zfmisc_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    k3_tarski(k1_tarski('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_72])).

tff(c_133,plain,(
    k2_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_81])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_30])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_28])).

tff(c_161,plain,(
    ! [A_41] :
      ( k2_xboole_0(k1_relat_1(A_41),k2_relat_1(A_41)) = k3_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,
    ( k2_xboole_0(k1_relat_1('#skF_1'),'#skF_1') = k3_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_161])).

tff(c_177,plain,(
    k3_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_133,c_54,c_170])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.95/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.19  
% 1.95/1.20  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.95/1.20  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.95/1.20  tff(f_61, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.95/1.20  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.95/1.20  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.20  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.95/1.20  tff(f_46, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.95/1.20  tff(f_48, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.95/1.20  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.95/1.20  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.95/1.20  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.20  tff(c_41, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.20  tff(c_45, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_41])).
% 1.95/1.20  tff(c_32, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.20  tff(c_53, plain, (k3_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_32])).
% 1.95/1.20  tff(c_46, plain, (![A_29]: (v1_relat_1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.20  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_46])).
% 1.95/1.20  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.20  tff(c_112, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.20  tff(c_124, plain, (![A_37]: (k3_tarski(k1_tarski(A_37))=k2_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 1.95/1.20  tff(c_20, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.20  tff(c_67, plain, (k1_zfmisc_1('#skF_1')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_20])).
% 1.95/1.20  tff(c_72, plain, (![A_30]: (k3_tarski(k1_zfmisc_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.20  tff(c_81, plain, (k3_tarski(k1_tarski('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_67, c_72])).
% 1.95/1.20  tff(c_133, plain, (k2_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_124, c_81])).
% 1.95/1.20  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.20  tff(c_54, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_30])).
% 1.95/1.20  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.20  tff(c_52, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_28])).
% 1.95/1.20  tff(c_161, plain, (![A_41]: (k2_xboole_0(k1_relat_1(A_41), k2_relat_1(A_41))=k3_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.20  tff(c_170, plain, (k2_xboole_0(k1_relat_1('#skF_1'), '#skF_1')=k3_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_161])).
% 1.95/1.20  tff(c_177, plain, (k3_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_133, c_54, c_170])).
% 1.95/1.20  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_177])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 41
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 0
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 1.95/1.20  
% 1.95/1.20  Ordering : KBO
% 1.95/1.20  
% 1.95/1.20  Simplification rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Subsume      : 0
% 1.95/1.20  #Demod        : 13
% 1.95/1.20  #Tautology    : 34
% 1.95/1.20  #SimpNegUnit  : 1
% 1.95/1.20  #BackRed      : 4
% 1.95/1.20  
% 1.95/1.20  #Partial instantiations: 0
% 1.95/1.20  #Strategies tried      : 1
% 1.95/1.20  
% 1.95/1.20  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.21  Preprocessing        : 0.30
% 1.95/1.21  Parsing              : 0.17
% 1.95/1.21  CNF conversion       : 0.02
% 1.95/1.21  Main loop            : 0.12
% 1.95/1.21  Inferencing          : 0.04
% 1.95/1.21  Reduction            : 0.04
% 1.95/1.21  Demodulation         : 0.03
% 1.95/1.21  BG Simplification    : 0.01
% 1.95/1.21  Subsumption          : 0.01
% 1.95/1.21  Abstraction          : 0.01
% 1.95/1.21  MUC search           : 0.00
% 1.95/1.21  Cooper               : 0.00
% 1.95/1.21  Total                : 0.44
% 1.95/1.21  Index Insertion      : 0.00
% 1.95/1.21  Index Deletion       : 0.00
% 1.95/1.21  Index Matching       : 0.00
% 1.95/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
