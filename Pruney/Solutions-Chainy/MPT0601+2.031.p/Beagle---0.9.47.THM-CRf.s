%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 128 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_3'))
    | k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_72,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(k2_tarski(A_46,C_47),B_48)
      | r2_hidden(C_47,B_48)
      | r2_hidden(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_145,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_26,plain,(
    ! [A_23,B_25] :
      ( k7_relat_1(A_23,B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,k1_relat_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_155,plain,(
    ! [A_54,A_55] :
      ( k7_relat_1(A_54,k1_tarski(A_55)) = k1_xboole_0
      | ~ v1_relat_1(A_54)
      | r2_hidden(A_55,k1_relat_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_145,c_26])).

tff(c_38,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_38])).

tff(c_162,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_82])).

tff(c_169,plain,(
    k7_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_162])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_2')) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_14])).

tff(c_178,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_174])).

tff(c_12,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_183,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_12])).

tff(c_190,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_183])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_190])).

tff(c_193,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_215,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_223,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_215])).

tff(c_194,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_349,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski(A_96,'#skF_1'(A_96,B_97,C_98)),C_98)
      | ~ r2_hidden(A_96,k10_relat_1(C_98,B_97))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_394,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(A_102,B_103,C_104),k11_relat_1(C_104,A_102))
      | ~ r2_hidden(A_102,k10_relat_1(C_104,B_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_349,c_30])).

tff(c_401,plain,(
    ! [B_103] :
      ( r2_hidden('#skF_1'('#skF_2',B_103,'#skF_3'),k1_xboole_0)
      | ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',B_103))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_394])).

tff(c_404,plain,(
    ! [B_103] :
      ( r2_hidden('#skF_1'('#skF_2',B_103,'#skF_3'),k1_xboole_0)
      | ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',B_103)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_401])).

tff(c_406,plain,(
    ! [B_105] : ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',B_105)) ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_404])).

tff(c_410,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_193,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.31  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.41/1.31  
% 2.41/1.31  %Foreground sorts:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Background operators:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Foreground operators:
% 2.41/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.41/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.31  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.31  
% 2.41/1.33  tff(f_94, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.41/1.33  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.41/1.33  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.33  tff(f_46, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.41/1.33  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.41/1.33  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.41/1.33  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.41/1.33  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.41/1.33  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.41/1.33  tff(f_36, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.41/1.33  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.41/1.33  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.41/1.33  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.41/1.33  tff(c_44, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3')) | k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.41/1.33  tff(c_72, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.41/1.33  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.41/1.33  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.33  tff(c_131, plain, (![A_46, C_47, B_48]: (r1_xboole_0(k2_tarski(A_46, C_47), B_48) | r2_hidden(C_47, B_48) | r2_hidden(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.33  tff(c_145, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53) | r2_hidden(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 2.41/1.33  tff(c_26, plain, (![A_23, B_25]: (k7_relat_1(A_23, B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, k1_relat_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.41/1.33  tff(c_155, plain, (![A_54, A_55]: (k7_relat_1(A_54, k1_tarski(A_55))=k1_xboole_0 | ~v1_relat_1(A_54) | r2_hidden(A_55, k1_relat_1(A_54)))), inference(resolution, [status(thm)], [c_145, c_26])).
% 2.41/1.33  tff(c_38, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.41/1.33  tff(c_82, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_38])).
% 2.41/1.33  tff(c_162, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_155, c_82])).
% 2.41/1.33  tff(c_169, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_162])).
% 2.41/1.33  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.41/1.33  tff(c_174, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_169, c_14])).
% 2.41/1.33  tff(c_178, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_174])).
% 2.41/1.33  tff(c_12, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.33  tff(c_183, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_12])).
% 2.41/1.33  tff(c_190, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_183])).
% 2.41/1.33  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_190])).
% 2.41/1.33  tff(c_193, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 2.41/1.33  tff(c_24, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.33  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.33  tff(c_215, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.41/1.33  tff(c_223, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_215])).
% 2.41/1.33  tff(c_194, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.41/1.33  tff(c_349, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski(A_96, '#skF_1'(A_96, B_97, C_98)), C_98) | ~r2_hidden(A_96, k10_relat_1(C_98, B_97)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.33  tff(c_30, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.33  tff(c_394, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_1'(A_102, B_103, C_104), k11_relat_1(C_104, A_102)) | ~r2_hidden(A_102, k10_relat_1(C_104, B_103)) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_349, c_30])).
% 2.41/1.33  tff(c_401, plain, (![B_103]: (r2_hidden('#skF_1'('#skF_2', B_103, '#skF_3'), k1_xboole_0) | ~r2_hidden('#skF_2', k10_relat_1('#skF_3', B_103)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_394])).
% 2.41/1.33  tff(c_404, plain, (![B_103]: (r2_hidden('#skF_1'('#skF_2', B_103, '#skF_3'), k1_xboole_0) | ~r2_hidden('#skF_2', k10_relat_1('#skF_3', B_103)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_401])).
% 2.41/1.33  tff(c_406, plain, (![B_105]: (~r2_hidden('#skF_2', k10_relat_1('#skF_3', B_105)))), inference(negUnitSimplification, [status(thm)], [c_223, c_404])).
% 2.41/1.33  tff(c_410, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_406])).
% 2.41/1.33  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_193, c_410])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 79
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 3
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 10
% 2.41/1.33  #Demod        : 13
% 2.41/1.33  #Tautology    : 33
% 2.41/1.33  #SimpNegUnit  : 6
% 2.41/1.33  #BackRed      : 0
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.31
% 2.41/1.33  Parsing              : 0.16
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.33  Main loop            : 0.25
% 2.41/1.33  Inferencing          : 0.10
% 2.41/1.33  Reduction            : 0.06
% 2.41/1.33  Demodulation         : 0.04
% 2.41/1.33  BG Simplification    : 0.02
% 2.41/1.33  Subsumption          : 0.05
% 2.41/1.33  Abstraction          : 0.01
% 2.41/1.33  MUC search           : 0.00
% 2.41/1.33  Cooper               : 0.00
% 2.41/1.33  Total                : 0.60
% 2.41/1.33  Index Insertion      : 0.00
% 2.41/1.33  Index Deletion       : 0.00
% 2.41/1.33  Index Matching       : 0.00
% 2.41/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
