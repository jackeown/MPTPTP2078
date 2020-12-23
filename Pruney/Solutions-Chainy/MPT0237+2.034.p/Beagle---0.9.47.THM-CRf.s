%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   60 (  95 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  96 expanded)
%              Number of equality atoms :   41 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_218,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_203])).

tff(c_221,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_20,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [A_54,B_55] : r1_tarski(k1_tarski(A_54),k2_tarski(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_13] : r1_tarski(k1_tarski(A_13),k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_148,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_13] : k4_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_148])).

tff(c_215,plain,(
    ! [A_13] : k2_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k5_xboole_0(k1_tarski(A_13),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_203])).

tff(c_291,plain,(
    ! [A_87] : k2_xboole_0(k1_tarski(A_87),k1_tarski(A_87)) = k1_tarski(A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_215])).

tff(c_119,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = k2_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_297,plain,(
    ! [A_87] : k3_tarski(k1_tarski(k1_tarski(A_87))) = k1_tarski(A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_128])).

tff(c_109,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),k1_tarski(B_62))
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k1_tarski(A_85),k1_tarski(B_86)) = k1_tarski(A_85)
      | B_86 = A_85 ) ),
    inference(resolution,[status(thm)],[c_109,c_14])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_357,plain,(
    ! [B_102,A_103] :
      ( k5_xboole_0(k1_tarski(B_102),k1_tarski(A_103)) = k2_xboole_0(k1_tarski(B_102),k1_tarski(A_103))
      | B_102 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_18])).

tff(c_40,plain,(
    ! [A_47,B_48] :
      ( k5_xboole_0(k1_tarski(A_47),k1_tarski(B_48)) = k2_tarski(A_47,B_48)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_372,plain,(
    ! [B_104,A_105] :
      ( k2_xboole_0(k1_tarski(B_104),k1_tarski(A_105)) = k2_tarski(B_104,A_105)
      | B_104 = A_105
      | B_104 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_40])).

tff(c_34,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_402,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_43])).

tff(c_408,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_402,c_43])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_128,c_20,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  
% 2.36/1.32  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.36/1.32  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.36/1.32  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.36/1.32  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.32  tff(f_61, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.36/1.32  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.36/1.32  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.36/1.32  tff(f_66, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.36/1.32  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.36/1.32  tff(f_71, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.36/1.32  tff(f_74, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.36/1.32  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.32  tff(c_12, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.32  tff(c_203, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.32  tff(c_218, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_203])).
% 2.36/1.32  tff(c_221, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_218])).
% 2.36/1.32  tff(c_20, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.32  tff(c_102, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), k2_tarski(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.36/1.32  tff(c_105, plain, (![A_13]: (r1_tarski(k1_tarski(A_13), k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_102])).
% 2.36/1.32  tff(c_148, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.32  tff(c_158, plain, (![A_13]: (k4_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_148])).
% 2.36/1.32  tff(c_215, plain, (![A_13]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k5_xboole_0(k1_tarski(A_13), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_158, c_203])).
% 2.36/1.32  tff(c_291, plain, (![A_87]: (k2_xboole_0(k1_tarski(A_87), k1_tarski(A_87))=k1_tarski(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_215])).
% 2.36/1.32  tff(c_119, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.32  tff(c_128, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=k2_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 2.36/1.32  tff(c_297, plain, (![A_87]: (k3_tarski(k1_tarski(k1_tarski(A_87)))=k1_tarski(A_87))), inference(superposition, [status(thm), theory('equality')], [c_291, c_128])).
% 2.36/1.32  tff(c_109, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), k1_tarski(B_62)) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.32  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.32  tff(c_269, plain, (![A_85, B_86]: (k4_xboole_0(k1_tarski(A_85), k1_tarski(B_86))=k1_tarski(A_85) | B_86=A_85)), inference(resolution, [status(thm)], [c_109, c_14])).
% 2.36/1.32  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.32  tff(c_357, plain, (![B_102, A_103]: (k5_xboole_0(k1_tarski(B_102), k1_tarski(A_103))=k2_xboole_0(k1_tarski(B_102), k1_tarski(A_103)) | B_102=A_103)), inference(superposition, [status(thm), theory('equality')], [c_269, c_18])).
% 2.36/1.32  tff(c_40, plain, (![A_47, B_48]: (k5_xboole_0(k1_tarski(A_47), k1_tarski(B_48))=k2_tarski(A_47, B_48) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.32  tff(c_372, plain, (![B_104, A_105]: (k2_xboole_0(k1_tarski(B_104), k1_tarski(A_105))=k2_tarski(B_104, A_105) | B_104=A_105 | B_104=A_105)), inference(superposition, [status(thm), theory('equality')], [c_357, c_40])).
% 2.36/1.32  tff(c_34, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.32  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.32  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.36/1.32  tff(c_402, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_372, c_43])).
% 2.36/1.32  tff(c_408, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_402, c_43])).
% 2.36/1.32  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_128, c_20, c_408])).
% 2.36/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  Inference rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Ref     : 0
% 2.36/1.32  #Sup     : 84
% 2.36/1.32  #Fact    : 0
% 2.36/1.32  #Define  : 0
% 2.36/1.32  #Split   : 0
% 2.36/1.32  #Chain   : 0
% 2.36/1.32  #Close   : 0
% 2.36/1.32  
% 2.36/1.32  Ordering : KBO
% 2.36/1.32  
% 2.36/1.32  Simplification rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Subsume      : 0
% 2.36/1.32  #Demod        : 22
% 2.36/1.32  #Tautology    : 70
% 2.36/1.32  #SimpNegUnit  : 0
% 2.36/1.32  #BackRed      : 1
% 2.36/1.32  
% 2.36/1.32  #Partial instantiations: 0
% 2.36/1.32  #Strategies tried      : 1
% 2.36/1.32  
% 2.36/1.32  Timing (in seconds)
% 2.36/1.32  ----------------------
% 2.36/1.32  Preprocessing        : 0.32
% 2.36/1.32  Parsing              : 0.17
% 2.36/1.32  CNF conversion       : 0.02
% 2.36/1.32  Main loop            : 0.21
% 2.36/1.32  Inferencing          : 0.09
% 2.36/1.32  Reduction            : 0.07
% 2.36/1.32  Demodulation         : 0.05
% 2.36/1.32  BG Simplification    : 0.02
% 2.36/1.32  Subsumption          : 0.03
% 2.36/1.32  Abstraction          : 0.02
% 2.36/1.32  MUC search           : 0.00
% 2.36/1.32  Cooper               : 0.00
% 2.36/1.32  Total                : 0.56
% 2.36/1.32  Index Insertion      : 0.00
% 2.36/1.32  Index Deletion       : 0.00
% 2.36/1.32  Index Matching       : 0.00
% 2.36/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
