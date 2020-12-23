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
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   55 (  56 expanded)
%              Number of leaves         :   34 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  50 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_42,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_260,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_2'(A_78,B_79,C_80),B_79)
      | ~ r2_hidden(A_78,k10_relat_1(C_80,B_79))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_59,B_60] : k3_xboole_0(k1_tarski(A_59),k2_tarski(A_59,B_60)) = k1_tarski(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_59,B_60] : k5_xboole_0(k1_tarski(A_59),k1_tarski(A_59)) = k4_xboole_0(k1_tarski(A_59),k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_4])).

tff(c_157,plain,(
    ! [A_64,B_65] : k4_xboole_0(k1_tarski(A_64),k2_tarski(A_64,B_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_164,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_28,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_28])).

tff(c_103,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tarski(A_54),B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_54] :
      ( k1_tarski(A_54) = k1_xboole_0
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_175,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_112])).

tff(c_266,plain,(
    ! [A_81,C_82] :
      ( ~ r2_hidden(A_81,k10_relat_1(C_82,k1_xboole_0))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_260,c_175])).

tff(c_277,plain,(
    ! [C_83] :
      ( ~ v1_relat_1(C_83)
      | k10_relat_1(C_83,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_266])).

tff(c_280,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_277])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.28  
% 2.06/1.29  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.06/1.29  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.29  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.06/1.29  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.29  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.06/1.29  tff(f_59, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.06/1.29  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.06/1.29  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.06/1.29  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.06/1.29  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.06/1.29  tff(c_42, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.06/1.29  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.06/1.29  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.29  tff(c_260, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_2'(A_78, B_79, C_80), B_79) | ~r2_hidden(A_78, k10_relat_1(C_80, B_79)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.06/1.29  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.29  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.29  tff(c_132, plain, (![A_59, B_60]: (k3_xboole_0(k1_tarski(A_59), k2_tarski(A_59, B_60))=k1_tarski(A_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.29  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.29  tff(c_138, plain, (![A_59, B_60]: (k5_xboole_0(k1_tarski(A_59), k1_tarski(A_59))=k4_xboole_0(k1_tarski(A_59), k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_4])).
% 2.06/1.29  tff(c_157, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), k2_tarski(A_64, B_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_138])).
% 2.06/1.29  tff(c_164, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 2.06/1.29  tff(c_28, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_167, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_28])).
% 2.06/1.29  tff(c_103, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.29  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.29  tff(c_112, plain, (![A_54]: (k1_tarski(A_54)=k1_xboole_0 | ~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_103, c_6])).
% 2.06/1.29  tff(c_175, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_167, c_112])).
% 2.06/1.29  tff(c_266, plain, (![A_81, C_82]: (~r2_hidden(A_81, k10_relat_1(C_82, k1_xboole_0)) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_260, c_175])).
% 2.06/1.29  tff(c_277, plain, (![C_83]: (~v1_relat_1(C_83) | k10_relat_1(C_83, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_266])).
% 2.06/1.29  tff(c_280, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_277])).
% 2.06/1.29  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_280])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 52
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 0
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 0
% 2.06/1.29  #Demod        : 8
% 2.06/1.29  #Tautology    : 41
% 2.06/1.29  #SimpNegUnit  : 4
% 2.06/1.29  #BackRed      : 2
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.34
% 2.06/1.29  Parsing              : 0.18
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.16
% 2.06/1.29  Inferencing          : 0.07
% 2.06/1.29  Reduction            : 0.05
% 2.06/1.29  Demodulation         : 0.04
% 2.06/1.30  BG Simplification    : 0.01
% 2.06/1.30  Subsumption          : 0.02
% 2.06/1.30  Abstraction          : 0.01
% 2.06/1.30  MUC search           : 0.00
% 2.06/1.30  Cooper               : 0.00
% 2.06/1.30  Total                : 0.53
% 2.06/1.30  Index Insertion      : 0.00
% 2.06/1.30  Index Deletion       : 0.00
% 2.06/1.30  Index Matching       : 0.00
% 2.06/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
