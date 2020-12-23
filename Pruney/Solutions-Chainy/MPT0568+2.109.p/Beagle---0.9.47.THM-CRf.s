%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  69 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_82,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_57,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_59,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_57])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    ! [A_50] :
      ( k10_relat_1(A_50,k2_relat_1(A_50)) = k1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_89,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_38,c_85])).

tff(c_178,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k10_relat_1(B_81,A_82),k10_relat_1(B_81,k2_relat_1(B_81)))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_192,plain,(
    ! [A_82] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_82),k10_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_178])).

tff(c_217,plain,(
    ! [A_87] : r1_tarski(k10_relat_1(k1_xboole_0,A_87),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_89,c_192])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_55,C_56,B_57] :
      ( ~ r2_hidden(A_55,C_56)
      | ~ r1_xboole_0(k2_tarski(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_119,plain,(
    ! [B_62] : r1_xboole_0(k1_xboole_0,B_62) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_xboole_0(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(A_63,B_64)
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    ! [B_64] :
      ( k1_xboole_0 = B_64
      | ~ r1_tarski(B_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_129,c_14])).

tff(c_232,plain,(
    ! [A_87] : k10_relat_1(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_142])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.22/1.33  
% 2.22/1.33  %Foreground sorts:
% 2.22/1.33  
% 2.22/1.33  
% 2.22/1.33  %Background operators:
% 2.22/1.33  
% 2.22/1.33  
% 2.22/1.33  %Foreground operators:
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.33  
% 2.32/1.34  tff(f_94, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.32/1.34  tff(f_82, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.32/1.34  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.32/1.34  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.32/1.34  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 2.32/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.32/1.34  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.32/1.34  tff(f_80, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.32/1.34  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.32/1.34  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.32/1.34  tff(f_97, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.32/1.34  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.32/1.34  tff(c_57, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.34  tff(c_59, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_57])).
% 2.32/1.34  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.32/1.34  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.32/1.34  tff(c_76, plain, (![A_50]: (k10_relat_1(A_50, k2_relat_1(A_50))=k1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.32/1.34  tff(c_85, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_76])).
% 2.32/1.34  tff(c_89, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_59, c_38, c_85])).
% 2.32/1.34  tff(c_178, plain, (![B_81, A_82]: (r1_tarski(k10_relat_1(B_81, A_82), k10_relat_1(B_81, k2_relat_1(B_81))) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.32/1.34  tff(c_192, plain, (![A_82]: (r1_tarski(k10_relat_1(k1_xboole_0, A_82), k10_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_178])).
% 2.32/1.34  tff(c_217, plain, (![A_87]: (r1_tarski(k10_relat_1(k1_xboole_0, A_87), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_89, c_192])).
% 2.32/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.34  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.34  tff(c_96, plain, (![A_55, C_56, B_57]: (~r2_hidden(A_55, C_56) | ~r1_xboole_0(k2_tarski(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.34  tff(c_102, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.32/1.34  tff(c_119, plain, (![B_62]: (r1_xboole_0(k1_xboole_0, B_62))), inference(resolution, [status(thm)], [c_6, c_102])).
% 2.32/1.34  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_xboole_0(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.34  tff(c_129, plain, (![A_63, B_64]: (r1_xboole_0(A_63, B_64) | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_119, c_8])).
% 2.32/1.34  tff(c_14, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.34  tff(c_142, plain, (![B_64]: (k1_xboole_0=B_64 | ~r1_tarski(B_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_129, c_14])).
% 2.32/1.34  tff(c_232, plain, (![A_87]: (k10_relat_1(k1_xboole_0, A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_217, c_142])).
% 2.32/1.34  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.32/1.34  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_42])).
% 2.32/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  Inference rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Ref     : 0
% 2.32/1.34  #Sup     : 46
% 2.32/1.34  #Fact    : 0
% 2.32/1.34  #Define  : 0
% 2.32/1.34  #Split   : 0
% 2.32/1.34  #Chain   : 0
% 2.32/1.34  #Close   : 0
% 2.32/1.34  
% 2.32/1.34  Ordering : KBO
% 2.32/1.34  
% 2.32/1.34  Simplification rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Subsume      : 2
% 2.32/1.34  #Demod        : 21
% 2.32/1.34  #Tautology    : 27
% 2.32/1.34  #SimpNegUnit  : 0
% 2.32/1.34  #BackRed      : 2
% 2.32/1.34  
% 2.32/1.34  #Partial instantiations: 0
% 2.32/1.34  #Strategies tried      : 1
% 2.32/1.34  
% 2.32/1.34  Timing (in seconds)
% 2.32/1.34  ----------------------
% 2.32/1.35  Preprocessing        : 0.35
% 2.32/1.35  Parsing              : 0.19
% 2.32/1.35  CNF conversion       : 0.02
% 2.32/1.35  Main loop            : 0.16
% 2.32/1.35  Inferencing          : 0.06
% 2.32/1.35  Reduction            : 0.05
% 2.32/1.35  Demodulation         : 0.04
% 2.32/1.35  BG Simplification    : 0.01
% 2.32/1.35  Subsumption          : 0.03
% 2.32/1.35  Abstraction          : 0.01
% 2.32/1.35  MUC search           : 0.00
% 2.32/1.35  Cooper               : 0.00
% 2.32/1.35  Total                : 0.54
% 2.32/1.35  Index Insertion      : 0.00
% 2.32/1.35  Index Deletion       : 0.00
% 2.32/1.35  Index Matching       : 0.00
% 2.32/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
