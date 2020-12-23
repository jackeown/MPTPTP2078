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
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 213 expanded)
%              Number of leaves         :   39 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 286 expanded)
%              Number of equality atoms :   20 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_354,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),A_147)
      | r2_hidden('#skF_3'(A_147,B_148),B_148)
      | k3_tarski(A_147) = B_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_141,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_44,plain,(
    ! [C_55,B_54] : ~ r2_hidden(C_55,k4_xboole_0(B_54,k1_tarski(C_55))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_44])).

tff(c_387,plain,(
    ! [A_147] :
      ( r2_hidden('#skF_2'(A_147,k1_xboole_0),A_147)
      | k3_tarski(A_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_354,c_146])).

tff(c_54,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_5'(A_58),A_58)
      | v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_151,plain,(
    ! [C_99] : ~ r2_hidden(C_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_44])).

tff(c_156,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_1113,plain,(
    ! [A_202,B_203,C_204] :
      ( r2_hidden(k4_tarski(A_202,'#skF_8'(A_202,B_203,C_204)),C_204)
      | ~ r2_hidden(A_202,k10_relat_1(C_204,B_203))
      | ~ v1_relat_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1151,plain,(
    ! [A_202,B_203] :
      ( ~ r2_hidden(A_202,k10_relat_1(k1_xboole_0,B_203))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1113,c_146])).

tff(c_1164,plain,(
    ! [A_205,B_206] : ~ r2_hidden(A_205,k10_relat_1(k1_xboole_0,B_206)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1151])).

tff(c_1209,plain,(
    ! [B_206] : v1_relat_1(k10_relat_1(k1_xboole_0,B_206)) ),
    inference(resolution,[status(thm)],[c_54,c_1164])).

tff(c_60,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k4_tarski(A_76,'#skF_8'(A_76,B_77,C_78)),C_78)
      | ~ r2_hidden(A_76,k10_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1201,plain,(
    ! [A_76,B_206,B_77] :
      ( ~ r2_hidden(A_76,k10_relat_1(k10_relat_1(k1_xboole_0,B_206),B_77))
      | ~ v1_relat_1(k10_relat_1(k1_xboole_0,B_206)) ) ),
    inference(resolution,[status(thm)],[c_60,c_1164])).

tff(c_1708,plain,(
    ! [A_240,B_241,B_242] : ~ r2_hidden(A_240,k10_relat_1(k10_relat_1(k1_xboole_0,B_241),B_242)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1201])).

tff(c_1753,plain,(
    ! [B_241,B_242] : k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0,B_241),B_242)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_387,c_1708])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),A_34)
      | r2_hidden('#skF_3'(A_34,B_35),B_35)
      | k3_tarski(A_34) = B_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2352,plain,(
    ! [A_281,B_282] :
      ( r2_hidden('#skF_2'(A_281,k10_relat_1(k1_xboole_0,B_282)),A_281)
      | k3_tarski(A_281) = k10_relat_1(k1_xboole_0,B_282) ) ),
    inference(resolution,[status(thm)],[c_36,c_1164])).

tff(c_1707,plain,(
    ! [A_76,B_206,B_77] : ~ r2_hidden(A_76,k10_relat_1(k10_relat_1(k1_xboole_0,B_206),B_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1201])).

tff(c_2368,plain,(
    ! [B_206,B_77,B_282] : k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0,B_206),B_77)) = k10_relat_1(k1_xboole_0,B_282) ),
    inference(resolution,[status(thm)],[c_2352,c_1707])).

tff(c_2424,plain,(
    ! [B_282] : k10_relat_1(k1_xboole_0,B_282) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_2368])).

tff(c_64,plain,(
    k10_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.91  
% 4.23/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.91  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1
% 4.23/1.91  
% 4.23/1.91  %Foreground sorts:
% 4.23/1.91  
% 4.23/1.91  
% 4.23/1.91  %Background operators:
% 4.23/1.91  
% 4.23/1.91  
% 4.23/1.91  %Foreground operators:
% 4.23/1.91  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.23/1.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.23/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.23/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.91  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.23/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.23/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.23/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.91  tff('#skF_9', type, '#skF_9': $i).
% 4.23/1.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.91  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.23/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.23/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.23/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.23/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.91  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.23/1.91  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.23/1.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.23/1.91  
% 4.23/1.92  tff(f_55, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 4.23/1.92  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.23/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.23/1.92  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.23/1.92  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.23/1.92  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 4.23/1.92  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 4.23/1.92  tff(f_89, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 4.23/1.92  tff(c_354, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), A_147) | r2_hidden('#skF_3'(A_147, B_148), B_148) | k3_tarski(A_147)=B_148)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.23/1.92  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.92  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.92  tff(c_128, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.23/1.92  tff(c_137, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 4.23/1.92  tff(c_141, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_137])).
% 4.23/1.92  tff(c_44, plain, (![C_55, B_54]: (~r2_hidden(C_55, k4_xboole_0(B_54, k1_tarski(C_55))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.23/1.92  tff(c_146, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_44])).
% 4.23/1.92  tff(c_387, plain, (![A_147]: (r2_hidden('#skF_2'(A_147, k1_xboole_0), A_147) | k3_tarski(A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_354, c_146])).
% 4.23/1.92  tff(c_54, plain, (![A_58]: (r2_hidden('#skF_5'(A_58), A_58) | v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.23/1.92  tff(c_151, plain, (![C_99]: (~r2_hidden(C_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_44])).
% 4.23/1.92  tff(c_156, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_151])).
% 4.23/1.92  tff(c_1113, plain, (![A_202, B_203, C_204]: (r2_hidden(k4_tarski(A_202, '#skF_8'(A_202, B_203, C_204)), C_204) | ~r2_hidden(A_202, k10_relat_1(C_204, B_203)) | ~v1_relat_1(C_204))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.23/1.92  tff(c_1151, plain, (![A_202, B_203]: (~r2_hidden(A_202, k10_relat_1(k1_xboole_0, B_203)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1113, c_146])).
% 4.23/1.92  tff(c_1164, plain, (![A_205, B_206]: (~r2_hidden(A_205, k10_relat_1(k1_xboole_0, B_206)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1151])).
% 4.23/1.92  tff(c_1209, plain, (![B_206]: (v1_relat_1(k10_relat_1(k1_xboole_0, B_206)))), inference(resolution, [status(thm)], [c_54, c_1164])).
% 4.23/1.92  tff(c_60, plain, (![A_76, B_77, C_78]: (r2_hidden(k4_tarski(A_76, '#skF_8'(A_76, B_77, C_78)), C_78) | ~r2_hidden(A_76, k10_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.23/1.92  tff(c_1201, plain, (![A_76, B_206, B_77]: (~r2_hidden(A_76, k10_relat_1(k10_relat_1(k1_xboole_0, B_206), B_77)) | ~v1_relat_1(k10_relat_1(k1_xboole_0, B_206)))), inference(resolution, [status(thm)], [c_60, c_1164])).
% 4.23/1.92  tff(c_1708, plain, (![A_240, B_241, B_242]: (~r2_hidden(A_240, k10_relat_1(k10_relat_1(k1_xboole_0, B_241), B_242)))), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1201])).
% 4.23/1.92  tff(c_1753, plain, (![B_241, B_242]: (k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0, B_241), B_242))=k1_xboole_0)), inference(resolution, [status(thm)], [c_387, c_1708])).
% 4.23/1.92  tff(c_36, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), A_34) | r2_hidden('#skF_3'(A_34, B_35), B_35) | k3_tarski(A_34)=B_35)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.23/1.92  tff(c_2352, plain, (![A_281, B_282]: (r2_hidden('#skF_2'(A_281, k10_relat_1(k1_xboole_0, B_282)), A_281) | k3_tarski(A_281)=k10_relat_1(k1_xboole_0, B_282))), inference(resolution, [status(thm)], [c_36, c_1164])).
% 4.23/1.92  tff(c_1707, plain, (![A_76, B_206, B_77]: (~r2_hidden(A_76, k10_relat_1(k10_relat_1(k1_xboole_0, B_206), B_77)))), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1201])).
% 4.23/1.92  tff(c_2368, plain, (![B_206, B_77, B_282]: (k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0, B_206), B_77))=k10_relat_1(k1_xboole_0, B_282))), inference(resolution, [status(thm)], [c_2352, c_1707])).
% 4.23/1.92  tff(c_2424, plain, (![B_282]: (k10_relat_1(k1_xboole_0, B_282)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_2368])).
% 4.23/1.92  tff(c_64, plain, (k10_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.23/1.92  tff(c_2470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2424, c_64])).
% 4.23/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.92  
% 4.23/1.92  Inference rules
% 4.23/1.92  ----------------------
% 4.23/1.92  #Ref     : 1
% 4.23/1.92  #Sup     : 500
% 4.23/1.92  #Fact    : 0
% 4.23/1.92  #Define  : 0
% 4.23/1.92  #Split   : 0
% 4.23/1.92  #Chain   : 0
% 4.23/1.92  #Close   : 0
% 4.23/1.92  
% 4.23/1.92  Ordering : KBO
% 4.23/1.92  
% 4.23/1.92  Simplification rules
% 4.23/1.92  ----------------------
% 4.23/1.92  #Subsume      : 129
% 4.23/1.92  #Demod        : 290
% 4.23/1.92  #Tautology    : 158
% 4.23/1.92  #SimpNegUnit  : 32
% 4.23/1.92  #BackRed      : 23
% 4.23/1.92  
% 4.23/1.92  #Partial instantiations: 0
% 4.23/1.92  #Strategies tried      : 1
% 4.23/1.92  
% 4.23/1.92  Timing (in seconds)
% 4.23/1.92  ----------------------
% 4.23/1.92  Preprocessing        : 0.44
% 4.23/1.92  Parsing              : 0.24
% 4.23/1.92  CNF conversion       : 0.03
% 4.23/1.92  Main loop            : 0.61
% 4.23/1.92  Inferencing          : 0.22
% 4.23/1.92  Reduction            : 0.18
% 4.23/1.92  Demodulation         : 0.12
% 4.23/1.92  BG Simplification    : 0.03
% 4.23/1.92  Subsumption          : 0.14
% 4.23/1.92  Abstraction          : 0.04
% 4.23/1.92  MUC search           : 0.00
% 4.23/1.92  Cooper               : 0.00
% 4.23/1.92  Total                : 1.09
% 4.23/1.92  Index Insertion      : 0.00
% 4.23/1.92  Index Deletion       : 0.00
% 4.23/1.92  Index Matching       : 0.00
% 4.23/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
