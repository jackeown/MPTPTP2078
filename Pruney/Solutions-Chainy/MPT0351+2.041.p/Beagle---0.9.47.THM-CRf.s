%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  73 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [B_37,A_38] : k3_tarski(k2_tarski(B_37,A_38)) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_14,plain,(
    ! [A_14,B_15] : k3_tarski(k2_tarski(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_19] : m1_subset_1(k2_subset_1(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_19] : m1_subset_1(A_19,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_294,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_subset_1(A_59,B_60,C_61) = k2_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_363,plain,(
    ! [A_64,B_65] :
      ( k4_subset_1(A_64,B_65,A_64) = k2_xboole_0(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_32,c_294])).

tff(c_367,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_363])).

tff(c_373,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_367])).

tff(c_28,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_28])).

tff(c_375,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_31])).

tff(c_219,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_219])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_6])).

tff(c_199,plain,(
    ! [A_48,B_49] :
      ( k3_subset_1(A_48,k3_subset_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_199])).

tff(c_266,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k3_subset_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_530,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,k3_subset_1(A_72,B_73)) = k3_subset_1(A_72,k3_subset_1(A_72,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_266,c_18])).

tff(c_534,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_530])).

tff(c_539,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_204,c_534])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_555,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_4])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.49/1.35  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.49/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.35  
% 2.60/1.36  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.60/1.36  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.60/1.36  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.60/1.36  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.60/1.36  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.60/1.36  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.60/1.36  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.60/1.36  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.60/1.36  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.60/1.36  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.60/1.36  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.60/1.36  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.36  tff(c_94, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.36  tff(c_109, plain, (![B_37, A_38]: (k3_tarski(k2_tarski(B_37, A_38))=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_94])).
% 2.60/1.36  tff(c_14, plain, (![A_14, B_15]: (k3_tarski(k2_tarski(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.36  tff(c_115, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14])).
% 2.60/1.36  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.36  tff(c_16, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.36  tff(c_20, plain, (![A_19]: (m1_subset_1(k2_subset_1(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.36  tff(c_32, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.60/1.36  tff(c_294, plain, (![A_59, B_60, C_61]: (k4_subset_1(A_59, B_60, C_61)=k2_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.36  tff(c_363, plain, (![A_64, B_65]: (k4_subset_1(A_64, B_65, A_64)=k2_xboole_0(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_32, c_294])).
% 2.60/1.36  tff(c_367, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_363])).
% 2.60/1.36  tff(c_373, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_367])).
% 2.60/1.36  tff(c_28, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.36  tff(c_31, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_28])).
% 2.60/1.36  tff(c_375, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_31])).
% 2.60/1.36  tff(c_219, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.36  tff(c_226, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_219])).
% 2.60/1.36  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.36  tff(c_231, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_226, c_6])).
% 2.60/1.36  tff(c_199, plain, (![A_48, B_49]: (k3_subset_1(A_48, k3_subset_1(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.36  tff(c_204, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_199])).
% 2.60/1.36  tff(c_266, plain, (![A_55, B_56]: (m1_subset_1(k3_subset_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.36  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.36  tff(c_530, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k3_subset_1(A_72, B_73))=k3_subset_1(A_72, k3_subset_1(A_72, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_266, c_18])).
% 2.60/1.36  tff(c_534, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_530])).
% 2.60/1.36  tff(c_539, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_204, c_534])).
% 2.60/1.36  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.36  tff(c_555, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_539, c_4])).
% 2.60/1.36  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_555])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 140
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 0
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 6
% 2.60/1.36  #Demod        : 43
% 2.60/1.36  #Tautology    : 89
% 2.60/1.36  #SimpNegUnit  : 1
% 2.60/1.36  #BackRed      : 4
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.37  Timing (in seconds)
% 2.60/1.37  ----------------------
% 2.60/1.37  Preprocessing        : 0.31
% 2.60/1.37  Parsing              : 0.17
% 2.60/1.37  CNF conversion       : 0.02
% 2.60/1.37  Main loop            : 0.29
% 2.60/1.37  Inferencing          : 0.10
% 2.60/1.37  Reduction            : 0.10
% 2.60/1.37  Demodulation         : 0.08
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.05
% 2.60/1.37  Abstraction          : 0.02
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.63
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
