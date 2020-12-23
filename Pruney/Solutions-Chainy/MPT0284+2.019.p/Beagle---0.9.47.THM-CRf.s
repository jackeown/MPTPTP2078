%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:29 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   47 (  72 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 103 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_34,B_35] : r1_tarski(k4_xboole_0(A_34,B_35),k5_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),k5_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_zfmisc_1(A_24),k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),k5_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k3_xboole_0(A_40,C_41),B_42)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [B_2,A_1,B_42] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_42)
      | ~ r1_tarski(A_1,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(k5_xboole_0(A_59,C_60),B_61)
      | ~ r1_tarski(C_60,B_61)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    ! [A_5,B_6,B_61] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),B_61)
      | ~ r1_tarski(k3_xboole_0(A_5,B_6),B_61)
      | ~ r1_tarski(A_5,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_228])).

tff(c_14,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_275,plain,(
    ! [A_73,B_74,B_75] :
      ( r1_tarski(k2_xboole_0(A_73,B_74),B_75)
      | ~ r1_tarski(k4_xboole_0(B_74,A_73),B_75)
      | ~ r1_tarski(A_73,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_228])).

tff(c_408,plain,(
    ! [B_93,A_94,B_95] :
      ( r1_tarski(k2_xboole_0(B_93,A_94),B_95)
      | ~ r1_tarski(B_93,B_95)
      | ~ r1_tarski(k3_xboole_0(A_94,B_93),B_95)
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_237,c_275])).

tff(c_423,plain,(
    ! [A_96,B_97,B_98] :
      ( r1_tarski(k2_xboole_0(A_96,B_97),B_98)
      | ~ r1_tarski(B_97,B_98)
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(resolution,[status(thm)],[c_150,c_408])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_427,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_423,c_24])).

tff(c_428,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_431,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_431])).

tff(c_436,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_440,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_436])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.23/1.33  
% 2.23/1.33  %Foreground sorts:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Background operators:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Foreground operators:
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.33  
% 2.52/1.34  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.52/1.34  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 2.52/1.34  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.52/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.52/1.34  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.52/1.34  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.52/1.34  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.52/1.34  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.52/1.34  tff(f_58, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 2.52/1.34  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.34  tff(c_109, plain, (![A_34, B_35]: (r1_tarski(k4_xboole_0(A_34, B_35), k5_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.34  tff(c_112, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), k5_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_109])).
% 2.52/1.34  tff(c_22, plain, (![A_24, B_25]: (r1_tarski(k1_zfmisc_1(A_24), k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.34  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), k5_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.34  tff(c_147, plain, (![A_40, C_41, B_42]: (r1_tarski(k3_xboole_0(A_40, C_41), B_42) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.34  tff(c_150, plain, (![B_2, A_1, B_42]: (r1_tarski(k3_xboole_0(B_2, A_1), B_42) | ~r1_tarski(A_1, B_42))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.52/1.34  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.34  tff(c_228, plain, (![A_59, C_60, B_61]: (r1_tarski(k5_xboole_0(A_59, C_60), B_61) | ~r1_tarski(C_60, B_61) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.34  tff(c_237, plain, (![A_5, B_6, B_61]: (r1_tarski(k4_xboole_0(A_5, B_6), B_61) | ~r1_tarski(k3_xboole_0(A_5, B_6), B_61) | ~r1_tarski(A_5, B_61))), inference(superposition, [status(thm), theory('equality')], [c_6, c_228])).
% 2.52/1.34  tff(c_14, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.34  tff(c_275, plain, (![A_73, B_74, B_75]: (r1_tarski(k2_xboole_0(A_73, B_74), B_75) | ~r1_tarski(k4_xboole_0(B_74, A_73), B_75) | ~r1_tarski(A_73, B_75))), inference(superposition, [status(thm), theory('equality')], [c_14, c_228])).
% 2.52/1.34  tff(c_408, plain, (![B_93, A_94, B_95]: (r1_tarski(k2_xboole_0(B_93, A_94), B_95) | ~r1_tarski(B_93, B_95) | ~r1_tarski(k3_xboole_0(A_94, B_93), B_95) | ~r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_237, c_275])).
% 2.52/1.34  tff(c_423, plain, (![A_96, B_97, B_98]: (r1_tarski(k2_xboole_0(A_96, B_97), B_98) | ~r1_tarski(B_97, B_98) | ~r1_tarski(A_96, B_98))), inference(resolution, [status(thm)], [c_150, c_408])).
% 2.52/1.34  tff(c_24, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.52/1.34  tff(c_427, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_423, c_24])).
% 2.52/1.34  tff(c_428, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_427])).
% 2.52/1.34  tff(c_431, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_428])).
% 2.52/1.34  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_431])).
% 2.52/1.34  tff(c_436, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_427])).
% 2.52/1.34  tff(c_440, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_436])).
% 2.52/1.34  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_440])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 102
% 2.52/1.34  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 1
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 21
% 2.52/1.34  #Demod        : 34
% 2.52/1.34  #Tautology    : 44
% 2.52/1.34  #SimpNegUnit  : 0
% 2.52/1.34  #BackRed      : 0
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.35  Preprocessing        : 0.30
% 2.52/1.35  Parsing              : 0.16
% 2.52/1.35  CNF conversion       : 0.02
% 2.52/1.35  Main loop            : 0.29
% 2.52/1.35  Inferencing          : 0.11
% 2.52/1.35  Reduction            : 0.10
% 2.52/1.35  Demodulation         : 0.08
% 2.52/1.35  BG Simplification    : 0.01
% 2.52/1.35  Subsumption          : 0.04
% 2.52/1.35  Abstraction          : 0.01
% 2.52/1.35  MUC search           : 0.00
% 2.52/1.35  Cooper               : 0.00
% 2.52/1.35  Total                : 0.62
% 2.52/1.35  Index Insertion      : 0.00
% 2.52/1.35  Index Deletion       : 0.00
% 2.52/1.35  Index Matching       : 0.00
% 2.52/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
