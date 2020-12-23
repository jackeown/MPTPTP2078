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
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  66 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_58,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_127,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(A_14,k1_zfmisc_1(k3_tarski(A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | ~ r1_tarski(k1_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_31] : r2_hidden(A_31,k1_zfmisc_1(k3_tarski(k1_tarski(A_31)))) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(k3_tarski(k1_tarski(A_31)))) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_128,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_96])).

tff(c_91,plain,(
    ! [A_29] : r2_hidden(A_29,k1_zfmisc_1(k3_tarski(k1_tarski(A_29)))) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_129,plain,(
    ! [A_29] : r2_hidden(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_91])).

tff(c_22,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_29,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_20,plain,(
    ! [A_15] : k3_tarski(k1_zfmisc_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_148,plain,(
    ! [A_42] :
      ( k4_yellow_0(k2_yellow_1(A_42)) = k3_tarski(A_42)
      | ~ r2_hidden(k3_tarski(A_42),A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_157,plain,(
    ! [A_15] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_15))) = k3_tarski(k1_zfmisc_1(A_15))
      | ~ r2_hidden(A_15,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_148])).

tff(c_161,plain,(
    ! [A_15] :
      ( k4_yellow_0(k3_yellow_1(A_15)) = A_15
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_29,c_20,c_157])).

tff(c_162,plain,(
    ! [A_15] : k4_yellow_0(k3_yellow_1(A_15)) = A_15 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_161])).

tff(c_28,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  %$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2
% 2.02/1.33  
% 2.02/1.33  %Foreground sorts:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Background operators:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Foreground operators:
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.33  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.02/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.33  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.02/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.33  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.02/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.33  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.33  
% 2.02/1.34  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.02/1.34  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.02/1.34  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.02/1.34  tff(f_45, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.02/1.34  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.02/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.02/1.34  tff(f_49, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.02/1.34  tff(f_58, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.02/1.34  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.02/1.34  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.02/1.34  tff(f_61, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.02/1.34  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.34  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.34  tff(c_112, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.34  tff(c_124, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_112])).
% 2.02/1.34  tff(c_127, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_124])).
% 2.02/1.34  tff(c_18, plain, (![A_14]: (r1_tarski(A_14, k1_zfmisc_1(k3_tarski(A_14))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.34  tff(c_86, plain, (![A_29, B_30]: (r2_hidden(A_29, B_30) | ~r1_tarski(k1_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.34  tff(c_92, plain, (![A_31]: (r2_hidden(A_31, k1_zfmisc_1(k3_tarski(k1_tarski(A_31)))))), inference(resolution, [status(thm)], [c_18, c_86])).
% 2.02/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.34  tff(c_96, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(k3_tarski(k1_tarski(A_31)))))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.02/1.34  tff(c_128, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_96])).
% 2.02/1.34  tff(c_91, plain, (![A_29]: (r2_hidden(A_29, k1_zfmisc_1(k3_tarski(k1_tarski(A_29)))))), inference(resolution, [status(thm)], [c_18, c_86])).
% 2.02/1.34  tff(c_129, plain, (![A_29]: (r2_hidden(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_91])).
% 2.02/1.34  tff(c_22, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.34  tff(c_26, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.34  tff(c_29, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.02/1.34  tff(c_20, plain, (![A_15]: (k3_tarski(k1_zfmisc_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.34  tff(c_148, plain, (![A_42]: (k4_yellow_0(k2_yellow_1(A_42))=k3_tarski(A_42) | ~r2_hidden(k3_tarski(A_42), A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.34  tff(c_157, plain, (![A_15]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_15)))=k3_tarski(k1_zfmisc_1(A_15)) | ~r2_hidden(A_15, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_148])).
% 2.02/1.34  tff(c_161, plain, (![A_15]: (k4_yellow_0(k3_yellow_1(A_15))=A_15 | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_29, c_20, c_157])).
% 2.02/1.34  tff(c_162, plain, (![A_15]: (k4_yellow_0(k3_yellow_1(A_15))=A_15)), inference(negUnitSimplification, [status(thm)], [c_128, c_161])).
% 2.02/1.34  tff(c_28, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.34  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_28])).
% 2.02/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  Inference rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Ref     : 0
% 2.02/1.34  #Sup     : 28
% 2.02/1.34  #Fact    : 0
% 2.02/1.34  #Define  : 0
% 2.02/1.34  #Split   : 0
% 2.02/1.34  #Chain   : 0
% 2.02/1.34  #Close   : 0
% 2.02/1.34  
% 2.02/1.34  Ordering : KBO
% 2.02/1.34  
% 2.02/1.34  Simplification rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Subsume      : 1
% 2.02/1.34  #Demod        : 10
% 2.02/1.34  #Tautology    : 18
% 2.02/1.34  #SimpNegUnit  : 1
% 2.02/1.34  #BackRed      : 3
% 2.02/1.34  
% 2.02/1.34  #Partial instantiations: 0
% 2.02/1.34  #Strategies tried      : 1
% 2.02/1.34  
% 2.02/1.34  Timing (in seconds)
% 2.02/1.34  ----------------------
% 2.02/1.35  Preprocessing        : 0.40
% 2.02/1.35  Parsing              : 0.23
% 2.02/1.35  CNF conversion       : 0.02
% 2.02/1.35  Main loop            : 0.12
% 2.02/1.35  Inferencing          : 0.05
% 2.02/1.35  Reduction            : 0.04
% 2.02/1.35  Demodulation         : 0.03
% 2.02/1.35  BG Simplification    : 0.01
% 2.02/1.35  Subsumption          : 0.02
% 2.02/1.35  Abstraction          : 0.01
% 2.02/1.35  MUC search           : 0.00
% 2.02/1.35  Cooper               : 0.00
% 2.02/1.35  Total                : 0.55
% 2.02/1.35  Index Insertion      : 0.00
% 2.02/1.35  Index Deletion       : 0.00
% 2.02/1.35  Index Matching       : 0.00
% 2.02/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
