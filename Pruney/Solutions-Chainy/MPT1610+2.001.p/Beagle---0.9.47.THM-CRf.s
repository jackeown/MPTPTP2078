%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 (  95 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k1_zfmisc_1(k3_xboole_0(A,B)) = k3_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_75,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_28,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(k1_tarski(A_51),B_52) = B_52
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_249,plain,(
    ! [B_55,A_56] :
      ( k1_xboole_0 != B_55
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_46])).

tff(c_254,plain,(
    ! [A_57,C_58] :
      ( k1_zfmisc_1(A_57) != k1_xboole_0
      | ~ r1_tarski(C_58,A_57) ) ),
    inference(resolution,[status(thm)],[c_34,c_249])).

tff(c_258,plain,(
    ! [B_11] : k1_zfmisc_1(B_11) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_254])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1235,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r2_hidden('#skF_1'(A_116,B_117,C_118),C_118)
      | r2_hidden('#skF_2'(A_116,B_117,C_118),C_118)
      | k3_xboole_0(A_116,B_117) = C_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1706,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_2'(A_148,B_149,B_149),B_149)
      | k3_xboole_0(A_148,B_149) = B_149 ) ),
    inference(resolution,[status(thm)],[c_18,c_1235])).

tff(c_215,plain,(
    ! [B_52,A_51] :
      ( k1_xboole_0 != B_52
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_46])).

tff(c_1754,plain,(
    ! [B_150,A_151] :
      ( k1_xboole_0 != B_150
      | k3_xboole_0(A_151,B_150) = B_150 ) ),
    inference(resolution,[status(thm)],[c_1706,c_215])).

tff(c_221,plain,(
    ! [A_53,B_54] : k3_xboole_0(k1_zfmisc_1(A_53),k1_zfmisc_1(B_54)) = k1_zfmisc_1(k3_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_620,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,k1_zfmisc_1(A_79))
      | ~ r2_hidden(D_78,k1_zfmisc_1(k3_xboole_0(A_79,B_80))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_8])).

tff(c_731,plain,(
    ! [C_91,A_92,B_93] :
      ( r2_hidden(C_91,k1_zfmisc_1(A_92))
      | ~ r1_tarski(C_91,k3_xboole_0(A_92,B_93)) ) ),
    inference(resolution,[status(thm)],[c_34,c_620])).

tff(c_755,plain,(
    ! [A_92,B_93] : r2_hidden(k3_xboole_0(A_92,B_93),k1_zfmisc_1(A_92)) ),
    inference(resolution,[status(thm)],[c_28,c_731])).

tff(c_2040,plain,(
    ! [A_151] : r2_hidden(k1_xboole_0,k1_zfmisc_1(A_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_755])).

tff(c_50,plain,(
    ! [A_24] : k9_setfam_1(A_24) = k1_zfmisc_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [A_26] : k2_yellow_1(k9_setfam_1(A_26)) = k3_yellow_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_57,plain,(
    ! [A_26] : k2_yellow_1(k1_zfmisc_1(A_26)) = k3_yellow_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_260,plain,(
    ! [A_60] :
      ( k3_yellow_0(k2_yellow_1(A_60)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_269,plain,(
    ! [A_26] :
      ( k3_yellow_0(k3_yellow_1(A_26)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_260])).

tff(c_2730,plain,(
    ! [A_179] :
      ( k3_yellow_0(k3_yellow_1(A_179)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_269])).

tff(c_22,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2733,plain,(
    ! [A_179] :
      ( k1_zfmisc_1(A_179) = k1_xboole_0
      | k3_yellow_0(k3_yellow_1(A_179)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2730,c_22])).

tff(c_2742,plain,(
    ! [A_179] : k3_yellow_0(k3_yellow_1(A_179)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_2733])).

tff(c_56,plain,(
    k3_yellow_0(k3_yellow_1('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.77  
% 3.88/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.77  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.88/1.77  
% 3.88/1.77  %Foreground sorts:
% 3.88/1.77  
% 3.88/1.77  
% 3.88/1.77  %Background operators:
% 3.88/1.77  
% 3.88/1.77  
% 3.88/1.77  %Foreground operators:
% 3.88/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.88/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.88/1.77  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.88/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.77  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.88/1.77  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.88/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.88/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.77  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.88/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.88/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.88/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/1.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.88/1.77  
% 3.88/1.78  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.78  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.88/1.78  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.88/1.78  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.88/1.78  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.88/1.78  tff(f_64, axiom, (![A, B]: (k1_zfmisc_1(k3_xboole_0(A, B)) = k3_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 3.88/1.78  tff(f_66, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.88/1.78  tff(f_75, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.88/1.78  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.88/1.78  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.88/1.78  tff(f_78, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 3.88/1.78  tff(c_28, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.78  tff(c_34, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.88/1.78  tff(c_210, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)=B_52 | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.88/1.78  tff(c_46, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.88/1.78  tff(c_249, plain, (![B_55, A_56]: (k1_xboole_0!=B_55 | ~r2_hidden(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_210, c_46])).
% 3.88/1.78  tff(c_254, plain, (![A_57, C_58]: (k1_zfmisc_1(A_57)!=k1_xboole_0 | ~r1_tarski(C_58, A_57))), inference(resolution, [status(thm)], [c_34, c_249])).
% 3.88/1.78  tff(c_258, plain, (![B_11]: (k1_zfmisc_1(B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_254])).
% 3.88/1.78  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.88/1.78  tff(c_1235, plain, (![A_116, B_117, C_118]: (~r2_hidden('#skF_1'(A_116, B_117, C_118), C_118) | r2_hidden('#skF_2'(A_116, B_117, C_118), C_118) | k3_xboole_0(A_116, B_117)=C_118)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.88/1.78  tff(c_1706, plain, (![A_148, B_149]: (r2_hidden('#skF_2'(A_148, B_149, B_149), B_149) | k3_xboole_0(A_148, B_149)=B_149)), inference(resolution, [status(thm)], [c_18, c_1235])).
% 3.88/1.78  tff(c_215, plain, (![B_52, A_51]: (k1_xboole_0!=B_52 | ~r2_hidden(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_210, c_46])).
% 3.88/1.78  tff(c_1754, plain, (![B_150, A_151]: (k1_xboole_0!=B_150 | k3_xboole_0(A_151, B_150)=B_150)), inference(resolution, [status(thm)], [c_1706, c_215])).
% 3.88/1.78  tff(c_221, plain, (![A_53, B_54]: (k3_xboole_0(k1_zfmisc_1(A_53), k1_zfmisc_1(B_54))=k1_zfmisc_1(k3_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.88/1.78  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.88/1.78  tff(c_620, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, k1_zfmisc_1(A_79)) | ~r2_hidden(D_78, k1_zfmisc_1(k3_xboole_0(A_79, B_80))))), inference(superposition, [status(thm), theory('equality')], [c_221, c_8])).
% 3.88/1.78  tff(c_731, plain, (![C_91, A_92, B_93]: (r2_hidden(C_91, k1_zfmisc_1(A_92)) | ~r1_tarski(C_91, k3_xboole_0(A_92, B_93)))), inference(resolution, [status(thm)], [c_34, c_620])).
% 3.88/1.78  tff(c_755, plain, (![A_92, B_93]: (r2_hidden(k3_xboole_0(A_92, B_93), k1_zfmisc_1(A_92)))), inference(resolution, [status(thm)], [c_28, c_731])).
% 3.88/1.78  tff(c_2040, plain, (![A_151]: (r2_hidden(k1_xboole_0, k1_zfmisc_1(A_151)))), inference(superposition, [status(thm), theory('equality')], [c_1754, c_755])).
% 3.88/1.78  tff(c_50, plain, (![A_24]: (k9_setfam_1(A_24)=k1_zfmisc_1(A_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.88/1.78  tff(c_54, plain, (![A_26]: (k2_yellow_1(k9_setfam_1(A_26))=k3_yellow_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.88/1.78  tff(c_57, plain, (![A_26]: (k2_yellow_1(k1_zfmisc_1(A_26))=k3_yellow_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 3.88/1.78  tff(c_260, plain, (![A_60]: (k3_yellow_0(k2_yellow_1(A_60))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.88/1.78  tff(c_269, plain, (![A_26]: (k3_yellow_0(k3_yellow_1(A_26))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_260])).
% 3.88/1.78  tff(c_2730, plain, (![A_179]: (k3_yellow_0(k3_yellow_1(A_179))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_179)))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_269])).
% 3.88/1.78  tff(c_22, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.88/1.78  tff(c_2733, plain, (![A_179]: (k1_zfmisc_1(A_179)=k1_xboole_0 | k3_yellow_0(k3_yellow_1(A_179))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2730, c_22])).
% 3.88/1.78  tff(c_2742, plain, (![A_179]: (k3_yellow_0(k3_yellow_1(A_179))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_258, c_2733])).
% 3.88/1.78  tff(c_56, plain, (k3_yellow_0(k3_yellow_1('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.78  tff(c_2746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2742, c_56])).
% 3.88/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.78  
% 3.88/1.78  Inference rules
% 3.88/1.78  ----------------------
% 3.88/1.78  #Ref     : 1
% 3.88/1.78  #Sup     : 680
% 3.88/1.78  #Fact    : 0
% 3.88/1.78  #Define  : 0
% 3.88/1.78  #Split   : 0
% 3.88/1.78  #Chain   : 0
% 3.88/1.78  #Close   : 0
% 3.88/1.78  
% 3.88/1.78  Ordering : KBO
% 3.88/1.78  
% 3.88/1.78  Simplification rules
% 3.88/1.78  ----------------------
% 3.88/1.78  #Subsume      : 126
% 3.88/1.78  #Demod        : 250
% 3.88/1.78  #Tautology    : 278
% 3.88/1.78  #SimpNegUnit  : 15
% 3.88/1.78  #BackRed      : 1
% 3.88/1.78  
% 3.88/1.78  #Partial instantiations: 0
% 3.88/1.78  #Strategies tried      : 1
% 3.88/1.78  
% 3.88/1.78  Timing (in seconds)
% 3.88/1.78  ----------------------
% 4.22/1.79  Preprocessing        : 0.34
% 4.22/1.79  Parsing              : 0.17
% 4.22/1.79  CNF conversion       : 0.03
% 4.22/1.79  Main loop            : 0.63
% 4.22/1.79  Inferencing          : 0.20
% 4.22/1.79  Reduction            : 0.24
% 4.22/1.79  Demodulation         : 0.19
% 4.22/1.79  BG Simplification    : 0.03
% 4.22/1.79  Subsumption          : 0.12
% 4.22/1.79  Abstraction          : 0.03
% 4.22/1.79  MUC search           : 0.00
% 4.22/1.79  Cooper               : 0.00
% 4.22/1.79  Total                : 1.00
% 4.22/1.79  Index Insertion      : 0.00
% 4.22/1.79  Index Deletion       : 0.00
% 4.22/1.79  Index Matching       : 0.00
% 4.22/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
