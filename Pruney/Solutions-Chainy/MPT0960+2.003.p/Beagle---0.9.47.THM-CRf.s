%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   54 (  58 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  50 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_wellord2 > k1_setfam_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(B_73,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_26,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_248,plain,(
    ! [B_74,A_75] : k2_xboole_0(B_74,A_75) = k2_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_26])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [A_75,B_74] : r1_tarski(A_75,k2_xboole_0(B_74,A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_10])).

tff(c_32,plain,(
    ! [A_44] : v1_relat_1(k1_wellord2(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [B_46,A_45] :
      ( k2_wellord1(k1_wellord2(B_46),A_45) = k1_wellord2(A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_393,plain,(
    ! [A_92,B_93] :
      ( k3_xboole_0(A_92,k2_zfmisc_1(B_93,B_93)) = k2_wellord1(A_92,B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_28,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [B_66,A_67] : k3_xboole_0(B_66,A_67) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,B_62)
      | ~ r1_tarski(A_61,k3_xboole_0(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [B_62,C_63] : r1_tarski(k3_xboole_0(B_62,C_63),B_62) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_163,plain,(
    ! [B_66,A_67] : r1_tarski(k3_xboole_0(B_66,A_67),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_141])).

tff(c_832,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k2_wellord1(A_151,B_152),k2_zfmisc_1(B_152,B_152))
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_163])).

tff(c_837,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_wellord2(A_45),k2_zfmisc_1(A_45,A_45))
      | ~ v1_relat_1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_832])).

tff(c_1413,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k1_wellord2(A_190),k2_zfmisc_1(A_190,A_190))
      | ~ r1_tarski(A_190,B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_837])).

tff(c_1475,plain,(
    ! [A_75] : r1_tarski(k1_wellord2(A_75),k2_zfmisc_1(A_75,A_75)) ),
    inference(resolution,[status(thm)],[c_263,c_1413])).

tff(c_36,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_wellord2 > k1_setfam_1 > #skF_1
% 3.29/1.51  
% 3.29/1.51  %Foreground sorts:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Background operators:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Foreground operators:
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.51  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.29/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.29/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.29/1.51  
% 3.29/1.52  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.29/1.52  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.29/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.29/1.52  tff(f_62, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.29/1.52  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 3.29/1.52  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 3.29/1.52  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.29/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.52  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.29/1.52  tff(f_69, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 3.29/1.52  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.52  tff(c_89, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.52  tff(c_225, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(B_73, A_72))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 3.29/1.52  tff(c_26, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.52  tff(c_248, plain, (![B_74, A_75]: (k2_xboole_0(B_74, A_75)=k2_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_225, c_26])).
% 3.29/1.52  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.52  tff(c_263, plain, (![A_75, B_74]: (r1_tarski(A_75, k2_xboole_0(B_74, A_75)))), inference(superposition, [status(thm), theory('equality')], [c_248, c_10])).
% 3.29/1.52  tff(c_32, plain, (![A_44]: (v1_relat_1(k1_wellord2(A_44)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.52  tff(c_34, plain, (![B_46, A_45]: (k2_wellord1(k1_wellord2(B_46), A_45)=k1_wellord2(A_45) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.52  tff(c_393, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k2_zfmisc_1(B_93, B_93))=k2_wellord1(A_92, B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.52  tff(c_74, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.52  tff(c_113, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_12, c_74])).
% 3.29/1.52  tff(c_28, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.52  tff(c_148, plain, (![B_66, A_67]: (k3_xboole_0(B_66, A_67)=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_113, c_28])).
% 3.29/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.52  tff(c_136, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, B_62) | ~r1_tarski(A_61, k3_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.52  tff(c_141, plain, (![B_62, C_63]: (r1_tarski(k3_xboole_0(B_62, C_63), B_62))), inference(resolution, [status(thm)], [c_6, c_136])).
% 3.29/1.52  tff(c_163, plain, (![B_66, A_67]: (r1_tarski(k3_xboole_0(B_66, A_67), A_67))), inference(superposition, [status(thm), theory('equality')], [c_148, c_141])).
% 3.29/1.52  tff(c_832, plain, (![A_151, B_152]: (r1_tarski(k2_wellord1(A_151, B_152), k2_zfmisc_1(B_152, B_152)) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_393, c_163])).
% 3.29/1.52  tff(c_837, plain, (![A_45, B_46]: (r1_tarski(k1_wellord2(A_45), k2_zfmisc_1(A_45, A_45)) | ~v1_relat_1(k1_wellord2(B_46)) | ~r1_tarski(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_34, c_832])).
% 3.29/1.52  tff(c_1413, plain, (![A_190, B_191]: (r1_tarski(k1_wellord2(A_190), k2_zfmisc_1(A_190, A_190)) | ~r1_tarski(A_190, B_191))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_837])).
% 3.29/1.52  tff(c_1475, plain, (![A_75]: (r1_tarski(k1_wellord2(A_75), k2_zfmisc_1(A_75, A_75)))), inference(resolution, [status(thm)], [c_263, c_1413])).
% 3.29/1.52  tff(c_36, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.52  tff(c_1496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1475, c_36])).
% 3.29/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.52  
% 3.29/1.52  Inference rules
% 3.29/1.52  ----------------------
% 3.29/1.52  #Ref     : 0
% 3.29/1.52  #Sup     : 356
% 3.29/1.52  #Fact    : 0
% 3.29/1.52  #Define  : 0
% 3.29/1.52  #Split   : 0
% 3.29/1.52  #Chain   : 0
% 3.29/1.52  #Close   : 0
% 3.29/1.52  
% 3.29/1.52  Ordering : KBO
% 3.29/1.52  
% 3.29/1.52  Simplification rules
% 3.29/1.52  ----------------------
% 3.29/1.52  #Subsume      : 33
% 3.29/1.52  #Demod        : 78
% 3.29/1.52  #Tautology    : 119
% 3.29/1.52  #SimpNegUnit  : 0
% 3.29/1.52  #BackRed      : 1
% 3.29/1.52  
% 3.29/1.52  #Partial instantiations: 0
% 3.29/1.52  #Strategies tried      : 1
% 3.29/1.52  
% 3.29/1.52  Timing (in seconds)
% 3.29/1.52  ----------------------
% 3.29/1.52  Preprocessing        : 0.31
% 3.29/1.52  Parsing              : 0.16
% 3.29/1.52  CNF conversion       : 0.02
% 3.29/1.52  Main loop            : 0.46
% 3.29/1.52  Inferencing          : 0.15
% 3.29/1.52  Reduction            : 0.17
% 3.29/1.52  Demodulation         : 0.14
% 3.29/1.52  BG Simplification    : 0.02
% 3.29/1.52  Subsumption          : 0.09
% 3.29/1.52  Abstraction          : 0.02
% 3.29/1.52  MUC search           : 0.00
% 3.29/1.52  Cooper               : 0.00
% 3.29/1.52  Total                : 0.79
% 3.29/1.52  Index Insertion      : 0.00
% 3.29/1.52  Index Deletion       : 0.00
% 3.29/1.52  Index Matching       : 0.00
% 3.29/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
