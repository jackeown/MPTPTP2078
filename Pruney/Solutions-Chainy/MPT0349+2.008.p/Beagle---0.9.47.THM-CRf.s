%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:25 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   33 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

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

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_34,plain,(
    ! [A_44] : k1_subset_1(A_44) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_48] : m1_subset_1(k1_subset_1(A_48),k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45,plain,(
    ! [A_48] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_349,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_353,plain,(
    ! [A_48] : k4_xboole_0(A_48,k1_xboole_0) = k3_subset_1(A_48,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45,c_349])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_524,plain,(
    ! [A_81,B_82] : k5_xboole_0(k5_xboole_0(A_81,B_82),k2_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_567,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,k1_xboole_0),A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_524])).

tff(c_581,plain,(
    ! [A_83] : k3_xboole_0(A_83,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_567])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_586,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = k4_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_4])).

tff(c_598,plain,(
    ! [A_83] : k3_subset_1(A_83,k1_xboole_0) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_8,c_586])).

tff(c_36,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_44,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_43])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:32:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.26/1.30  
% 2.26/1.30  %Foreground sorts:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Background operators:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Foreground operators:
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.26/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.26/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.26/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.30  
% 2.26/1.31  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.26/1.31  tff(f_67, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.26/1.31  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.26/1.31  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.26/1.31  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.26/1.31  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.26/1.31  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.26/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.26/1.31  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.26/1.31  tff(f_70, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.26/1.31  tff(c_34, plain, (![A_44]: (k1_subset_1(A_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.31  tff(c_40, plain, (![A_48]: (m1_subset_1(k1_subset_1(A_48), k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.31  tff(c_45, plain, (![A_48]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 2.26/1.31  tff(c_349, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.31  tff(c_353, plain, (![A_48]: (k4_xboole_0(A_48, k1_xboole_0)=k3_subset_1(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_45, c_349])).
% 2.26/1.31  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.31  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.31  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.31  tff(c_524, plain, (![A_81, B_82]: (k5_xboole_0(k5_xboole_0(A_81, B_82), k2_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.31  tff(c_567, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, k1_xboole_0), A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_524])).
% 2.26/1.31  tff(c_581, plain, (![A_83]: (k3_xboole_0(A_83, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_567])).
% 2.26/1.31  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.31  tff(c_586, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=k4_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_581, c_4])).
% 2.26/1.31  tff(c_598, plain, (![A_83]: (k3_subset_1(A_83, k1_xboole_0)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_353, c_8, c_586])).
% 2.26/1.31  tff(c_36, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.31  tff(c_42, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.31  tff(c_43, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 2.26/1.31  tff(c_44, plain, (k3_subset_1('#skF_1', k1_xboole_0)!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_43])).
% 2.26/1.31  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_598, c_44])).
% 2.26/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  Inference rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Ref     : 0
% 2.26/1.31  #Sup     : 133
% 2.26/1.31  #Fact    : 0
% 2.26/1.31  #Define  : 0
% 2.26/1.31  #Split   : 0
% 2.26/1.31  #Chain   : 0
% 2.26/1.31  #Close   : 0
% 2.26/1.31  
% 2.26/1.31  Ordering : KBO
% 2.26/1.31  
% 2.26/1.31  Simplification rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Subsume      : 0
% 2.26/1.31  #Demod        : 87
% 2.26/1.31  #Tautology    : 90
% 2.26/1.31  #SimpNegUnit  : 0
% 2.26/1.31  #BackRed      : 4
% 2.26/1.31  
% 2.26/1.31  #Partial instantiations: 0
% 2.26/1.31  #Strategies tried      : 1
% 2.26/1.31  
% 2.26/1.31  Timing (in seconds)
% 2.26/1.31  ----------------------
% 2.26/1.32  Preprocessing        : 0.32
% 2.26/1.32  Parsing              : 0.17
% 2.26/1.32  CNF conversion       : 0.02
% 2.26/1.32  Main loop            : 0.24
% 2.26/1.32  Inferencing          : 0.09
% 2.26/1.32  Reduction            : 0.09
% 2.26/1.32  Demodulation         : 0.07
% 2.26/1.32  BG Simplification    : 0.02
% 2.26/1.32  Subsumption          : 0.03
% 2.26/1.32  Abstraction          : 0.02
% 2.26/1.32  MUC search           : 0.00
% 2.26/1.32  Cooper               : 0.00
% 2.26/1.32  Total                : 0.58
% 2.26/1.32  Index Insertion      : 0.00
% 2.26/1.32  Index Deletion       : 0.00
% 2.26/1.32  Index Matching       : 0.00
% 2.26/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
