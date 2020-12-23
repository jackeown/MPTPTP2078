%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:02 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_32,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | ~ r1_xboole_0(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_197,plain,(
    ! [A_80] : ~ r2_hidden(A_80,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_191])).

tff(c_202,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_197])).

tff(c_213,plain,(
    ! [B_84,A_85] :
      ( k3_xboole_0(B_84,k2_zfmisc_1(A_85,k2_relat_1(B_84))) = k7_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_168,plain,(
    ! [B_75] : k4_xboole_0(k1_xboole_0,B_75) = k3_xboole_0(k1_xboole_0,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_70])).

tff(c_177,plain,(
    ! [B_75] : k3_xboole_0(k1_xboole_0,B_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_168])).

tff(c_220,plain,(
    ! [A_85] :
      ( k7_relat_1(k1_xboole_0,A_85) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_177])).

tff(c_233,plain,(
    ! [A_85] : k7_relat_1(k1_xboole_0,A_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_220])).

tff(c_36,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.29  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.29  
% 2.02/1.29  %Foreground sorts:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Background operators:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Foreground operators:
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.29  
% 2.02/1.30  tff(f_64, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.30  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.30  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.02/1.30  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 2.02/1.30  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.02/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.02/1.30  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.02/1.30  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.02/1.30  tff(f_71, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.02/1.30  tff(c_32, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.30  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.30  tff(c_191, plain, (![A_77, C_78, B_79]: (~r2_hidden(A_77, C_78) | ~r1_xboole_0(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.30  tff(c_197, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_191])).
% 2.02/1.30  tff(c_202, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_197])).
% 2.02/1.30  tff(c_213, plain, (![B_84, A_85]: (k3_xboole_0(B_84, k2_zfmisc_1(A_85, k2_relat_1(B_84)))=k7_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.30  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.30  tff(c_161, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.30  tff(c_54, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.30  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.30  tff(c_70, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 2.02/1.30  tff(c_168, plain, (![B_75]: (k4_xboole_0(k1_xboole_0, B_75)=k3_xboole_0(k1_xboole_0, B_75))), inference(superposition, [status(thm), theory('equality')], [c_161, c_70])).
% 2.02/1.30  tff(c_177, plain, (![B_75]: (k3_xboole_0(k1_xboole_0, B_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_168])).
% 2.02/1.30  tff(c_220, plain, (![A_85]: (k7_relat_1(k1_xboole_0, A_85)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_177])).
% 2.02/1.30  tff(c_233, plain, (![A_85]: (k7_relat_1(k1_xboole_0, A_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_220])).
% 2.02/1.30  tff(c_36, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.02/1.30  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_36])).
% 2.02/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  Inference rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Ref     : 0
% 2.02/1.30  #Sup     : 44
% 2.02/1.30  #Fact    : 0
% 2.02/1.30  #Define  : 0
% 2.02/1.30  #Split   : 0
% 2.02/1.30  #Chain   : 0
% 2.02/1.30  #Close   : 0
% 2.02/1.30  
% 2.02/1.30  Ordering : KBO
% 2.02/1.30  
% 2.02/1.30  Simplification rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Subsume      : 0
% 2.02/1.30  #Demod        : 15
% 2.02/1.30  #Tautology    : 37
% 2.02/1.30  #SimpNegUnit  : 0
% 2.02/1.30  #BackRed      : 1
% 2.02/1.30  
% 2.02/1.30  #Partial instantiations: 0
% 2.02/1.30  #Strategies tried      : 1
% 2.02/1.30  
% 2.02/1.30  Timing (in seconds)
% 2.02/1.30  ----------------------
% 2.02/1.30  Preprocessing        : 0.31
% 2.02/1.30  Parsing              : 0.17
% 2.02/1.30  CNF conversion       : 0.02
% 2.02/1.30  Main loop            : 0.22
% 2.02/1.30  Inferencing          : 0.09
% 2.02/1.30  Reduction            : 0.08
% 2.02/1.30  Demodulation         : 0.06
% 2.02/1.30  BG Simplification    : 0.01
% 2.02/1.30  Subsumption          : 0.02
% 2.02/1.30  Abstraction          : 0.01
% 2.02/1.30  MUC search           : 0.00
% 2.02/1.30  Cooper               : 0.00
% 2.02/1.30  Total                : 0.56
% 2.02/1.30  Index Insertion      : 0.00
% 2.02/1.30  Index Deletion       : 0.00
% 2.02/1.30  Index Matching       : 0.00
% 2.02/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
