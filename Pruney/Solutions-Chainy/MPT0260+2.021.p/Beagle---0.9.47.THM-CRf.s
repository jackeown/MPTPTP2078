%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  80 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [A_65,B_66] : k3_xboole_0(k1_tarski(A_65),k2_tarski(A_65,B_66)) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_183,plain,(
    ! [A_68] : k3_xboole_0(k1_tarski(A_68),k1_tarski(A_68)) = k1_tarski(A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_68] : k5_xboole_0(k1_tarski(A_68),k1_tarski(A_68)) = k4_xboole_0(k1_tarski(A_68),k1_tarski(A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_8])).

tff(c_194,plain,(
    ! [A_68] : k4_xboole_0(k1_tarski(A_68),k1_tarski(A_68)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_189])).

tff(c_36,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_196,plain,(
    ! [B_48] : k1_tarski(B_48) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_36])).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [A_45,B_46] : k3_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(A_59,B_60)
      | k3_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [B_61,A_62] :
      ( r1_xboole_0(B_61,A_62)
      | k3_xboole_0(A_62,B_61) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_101,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_216,plain,(
    ! [B_73,A_74] :
      ( k3_xboole_0(B_73,A_74) = k1_xboole_0
      | k3_xboole_0(A_74,B_73) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_233,plain,(
    ! [A_13] : k3_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_216])).

tff(c_42,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_334,plain,(
    ! [A_85,B_86,C_87] : k3_xboole_0(k3_xboole_0(A_85,B_86),C_87) = k3_xboole_0(A_85,k3_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_381,plain,(
    ! [C_87] : k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_xboole_0('#skF_3',C_87)) = k3_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_334])).

tff(c_437,plain,(
    ! [C_93] : k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_xboole_0('#skF_3',C_93)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_381])).

tff(c_115,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(B_61,A_62) = k1_xboole_0
      | k3_xboole_0(A_62,B_61) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_511,plain,(
    ! [C_95] : k3_xboole_0(k3_xboole_0('#skF_3',C_95),k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_115])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k3_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k3_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_555,plain,(
    ! [C_96] : k3_xboole_0('#skF_3',k3_xboole_0(C_96,k2_tarski('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_12])).

tff(c_590,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_555])).

tff(c_32,plain,(
    ! [B_44,A_43] :
      ( k3_xboole_0(B_44,k1_tarski(A_43)) = k1_tarski(A_43)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_615,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_32])).

tff(c_630,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_615])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:02:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.43  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.43  
% 2.61/1.43  %Foreground sorts:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Background operators:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Foreground operators:
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  
% 2.61/1.45  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.61/1.45  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.45  tff(f_63, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.61/1.45  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.45  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.61/1.45  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.61/1.45  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.61/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.61/1.45  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.61/1.45  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.61/1.45  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.61/1.45  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.45  tff(c_18, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.45  tff(c_135, plain, (![A_65, B_66]: (k3_xboole_0(k1_tarski(A_65), k2_tarski(A_65, B_66))=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.45  tff(c_183, plain, (![A_68]: (k3_xboole_0(k1_tarski(A_68), k1_tarski(A_68))=k1_tarski(A_68))), inference(superposition, [status(thm), theory('equality')], [c_18, c_135])).
% 2.61/1.45  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.45  tff(c_189, plain, (![A_68]: (k5_xboole_0(k1_tarski(A_68), k1_tarski(A_68))=k4_xboole_0(k1_tarski(A_68), k1_tarski(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_8])).
% 2.61/1.45  tff(c_194, plain, (![A_68]: (k4_xboole_0(k1_tarski(A_68), k1_tarski(A_68))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_189])).
% 2.61/1.45  tff(c_36, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.45  tff(c_196, plain, (![B_48]: (k1_tarski(B_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_36])).
% 2.61/1.45  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.45  tff(c_34, plain, (![A_45, B_46]: (k3_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46))=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.45  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.45  tff(c_101, plain, (![A_59, B_60]: (r1_xboole_0(A_59, B_60) | k3_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.45  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.45  tff(c_109, plain, (![B_61, A_62]: (r1_xboole_0(B_61, A_62) | k3_xboole_0(A_62, B_61)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_6])).
% 2.61/1.45  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.45  tff(c_216, plain, (![B_73, A_74]: (k3_xboole_0(B_73, A_74)=k1_xboole_0 | k3_xboole_0(A_74, B_73)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.61/1.45  tff(c_233, plain, (![A_13]: (k3_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_216])).
% 2.61/1.45  tff(c_42, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.45  tff(c_84, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.45  tff(c_92, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_84])).
% 2.61/1.45  tff(c_334, plain, (![A_85, B_86, C_87]: (k3_xboole_0(k3_xboole_0(A_85, B_86), C_87)=k3_xboole_0(A_85, k3_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.45  tff(c_381, plain, (![C_87]: (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', C_87))=k3_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_92, c_334])).
% 2.61/1.45  tff(c_437, plain, (![C_93]: (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', C_93))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_381])).
% 2.61/1.45  tff(c_115, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k1_xboole_0 | k3_xboole_0(A_62, B_61)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.61/1.45  tff(c_511, plain, (![C_95]: (k3_xboole_0(k3_xboole_0('#skF_3', C_95), k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_115])).
% 2.61/1.45  tff(c_12, plain, (![A_10, B_11, C_12]: (k3_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k3_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.45  tff(c_555, plain, (![C_96]: (k3_xboole_0('#skF_3', k3_xboole_0(C_96, k2_tarski('#skF_1', '#skF_2')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_511, c_12])).
% 2.61/1.45  tff(c_590, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_555])).
% 2.61/1.45  tff(c_32, plain, (![B_44, A_43]: (k3_xboole_0(B_44, k1_tarski(A_43))=k1_tarski(A_43) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.45  tff(c_615, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_590, c_32])).
% 2.61/1.45  tff(c_630, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_615])).
% 2.61/1.45  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_630])).
% 2.61/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.45  
% 2.61/1.45  Inference rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Ref     : 0
% 2.61/1.45  #Sup     : 160
% 2.61/1.45  #Fact    : 0
% 2.61/1.45  #Define  : 0
% 2.61/1.45  #Split   : 0
% 2.61/1.45  #Chain   : 0
% 2.61/1.45  #Close   : 0
% 2.61/1.45  
% 2.61/1.45  Ordering : KBO
% 2.61/1.45  
% 2.61/1.45  Simplification rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Subsume      : 5
% 2.61/1.45  #Demod        : 67
% 2.61/1.45  #Tautology    : 102
% 2.61/1.45  #SimpNegUnit  : 6
% 2.61/1.45  #BackRed      : 1
% 2.61/1.45  
% 2.61/1.45  #Partial instantiations: 0
% 2.61/1.45  #Strategies tried      : 1
% 2.61/1.45  
% 2.61/1.45  Timing (in seconds)
% 2.61/1.45  ----------------------
% 2.61/1.45  Preprocessing        : 0.35
% 2.61/1.45  Parsing              : 0.19
% 2.61/1.45  CNF conversion       : 0.02
% 2.61/1.45  Main loop            : 0.28
% 2.61/1.45  Inferencing          : 0.10
% 2.61/1.45  Reduction            : 0.10
% 2.61/1.45  Demodulation         : 0.08
% 2.61/1.45  BG Simplification    : 0.02
% 2.61/1.45  Subsumption          : 0.04
% 2.61/1.45  Abstraction          : 0.02
% 2.61/1.45  MUC search           : 0.00
% 2.61/1.45  Cooper               : 0.00
% 2.61/1.45  Total                : 0.66
% 2.61/1.45  Index Insertion      : 0.00
% 2.61/1.45  Index Deletion       : 0.00
% 2.61/1.45  Index Matching       : 0.00
% 2.61/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
