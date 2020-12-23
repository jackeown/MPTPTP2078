%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 159 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k7_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k2_relat_1(B))
            & v1_finset_1(k10_relat_1(B,A)) )
         => v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_finset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
       => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
          & r1_tarski(A,k2_relat_1(C)) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(c_24,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    v1_finset_1(k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_funct_1(k7_relat_1(A_11,B_12))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [C_33,A_34,B_35] :
      ( r1_tarski(k10_relat_1(C_33,A_34),k10_relat_1(C_33,B_35))
      | ~ r1_tarski(A_34,B_35)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    ! [A_51,A_52] :
      ( r1_tarski(k10_relat_1(A_51,A_52),k1_relat_1(A_51))
      | ~ r1_tarski(A_52,k2_relat_1(A_51))
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k1_relat_1(k7_relat_1(B_10,A_9)) = A_9
      | ~ r1_tarski(A_9,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_51,A_52] :
      ( k1_relat_1(k7_relat_1(A_51,k10_relat_1(A_51,A_52))) = k10_relat_1(A_51,A_52)
      | ~ r1_tarski(A_52,k2_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_30] :
      ( v1_finset_1(k2_relat_1(A_30))
      | ~ v1_finset_1(k1_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_274,plain,(
    ! [B_70,A_71] :
      ( v1_finset_1(k9_relat_1(B_70,A_71))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(B_70,A_71)))
      | ~ v1_funct_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_1026,plain,(
    ! [A_153,A_154] :
      ( v1_finset_1(k9_relat_1(A_153,k10_relat_1(A_153,A_154)))
      | ~ v1_finset_1(k10_relat_1(A_153,A_154))
      | ~ v1_funct_1(k7_relat_1(A_153,k10_relat_1(A_153,A_154)))
      | ~ v1_relat_1(k7_relat_1(A_153,k10_relat_1(A_153,A_154)))
      | ~ v1_relat_1(A_153)
      | ~ r1_tarski(A_154,k2_relat_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_274])).

tff(c_1038,plain,(
    ! [A_155,A_156] :
      ( v1_finset_1(k9_relat_1(A_155,k10_relat_1(A_155,A_156)))
      | ~ v1_finset_1(k10_relat_1(A_155,A_156))
      | ~ v1_funct_1(k7_relat_1(A_155,k10_relat_1(A_155,A_156)))
      | ~ r1_tarski(A_156,k2_relat_1(A_155))
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_2,c_1026])).

tff(c_1084,plain,(
    ! [A_160,A_161] :
      ( v1_finset_1(k9_relat_1(A_160,k10_relat_1(A_160,A_161)))
      | ~ v1_finset_1(k10_relat_1(A_160,A_161))
      | ~ r1_tarski(A_161,k2_relat_1(A_160))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_12,c_1038])).

tff(c_83,plain,(
    ! [A_5,A_34] :
      ( r1_tarski(k10_relat_1(A_5,A_34),k1_relat_1(A_5))
      | ~ r1_tarski(A_34,k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,k10_relat_1(B_14,k9_relat_1(B_14,A_13)))
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_166,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,B_54)
      | ~ r1_tarski(A_53,k2_relat_1(C_55))
      | ~ r1_tarski(k10_relat_1(C_55,A_53),k10_relat_1(C_55,B_54))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_322,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,k9_relat_1(B_85,k10_relat_1(B_85,A_84)))
      | ~ r1_tarski(A_84,k2_relat_1(B_85))
      | ~ v1_funct_1(B_85)
      | ~ r1_tarski(k10_relat_1(B_85,A_84),k1_relat_1(B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_337,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,k9_relat_1(A_89,k10_relat_1(A_89,A_88)))
      | ~ v1_funct_1(A_89)
      | ~ r1_tarski(A_88,k2_relat_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_83,c_322])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( v1_finset_1(A_18)
      | ~ v1_finset_1(B_19)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_355,plain,(
    ! [A_88,A_89] :
      ( v1_finset_1(A_88)
      | ~ v1_finset_1(k9_relat_1(A_89,k10_relat_1(A_89,A_88)))
      | ~ v1_funct_1(A_89)
      | ~ r1_tarski(A_88,k2_relat_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_337,c_20])).

tff(c_1095,plain,(
    ! [A_162,A_163] :
      ( v1_finset_1(A_162)
      | ~ v1_finset_1(k10_relat_1(A_163,A_162))
      | ~ r1_tarski(A_162,k2_relat_1(A_163))
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_1084,c_355])).

tff(c_1101,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_finset_1(k10_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1095])).

tff(c_1104,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_1101])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.61  
% 3.64/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.61  %$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k7_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.64/1.61  
% 3.64/1.61  %Foreground sorts:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Background operators:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Foreground operators:
% 3.64/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.64/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.64/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.61  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 3.64/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.61  
% 3.64/1.63  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k2_relat_1(B)) & v1_finset_1(k10_relat_1(B, A))) => v1_finset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_finset_1)).
% 3.64/1.63  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.64/1.63  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.64/1.63  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.64/1.63  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.64/1.63  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.64/1.63  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.64/1.63  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) => v1_finset_1(k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 3.64/1.63  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.64/1.63  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.64/1.63  tff(f_79, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 3.64/1.63  tff(c_24, plain, (~v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.63  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.63  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.63  tff(c_26, plain, (v1_finset_1(k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.63  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.63  tff(c_12, plain, (![A_11, B_12]: (v1_funct_1(k7_relat_1(A_11, B_12)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.64/1.63  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.63  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.63  tff(c_74, plain, (![C_33, A_34, B_35]: (r1_tarski(k10_relat_1(C_33, A_34), k10_relat_1(C_33, B_35)) | ~r1_tarski(A_34, B_35) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.63  tff(c_151, plain, (![A_51, A_52]: (r1_tarski(k10_relat_1(A_51, A_52), k1_relat_1(A_51)) | ~r1_tarski(A_52, k2_relat_1(A_51)) | ~v1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 3.64/1.63  tff(c_10, plain, (![B_10, A_9]: (k1_relat_1(k7_relat_1(B_10, A_9))=A_9 | ~r1_tarski(A_9, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.63  tff(c_164, plain, (![A_51, A_52]: (k1_relat_1(k7_relat_1(A_51, k10_relat_1(A_51, A_52)))=k10_relat_1(A_51, A_52) | ~r1_tarski(A_52, k2_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_151, c_10])).
% 3.64/1.63  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.63  tff(c_63, plain, (![A_30]: (v1_finset_1(k2_relat_1(A_30)) | ~v1_finset_1(k1_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.64/1.63  tff(c_274, plain, (![B_70, A_71]: (v1_finset_1(k9_relat_1(B_70, A_71)) | ~v1_finset_1(k1_relat_1(k7_relat_1(B_70, A_71))) | ~v1_funct_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63])).
% 3.64/1.63  tff(c_1026, plain, (![A_153, A_154]: (v1_finset_1(k9_relat_1(A_153, k10_relat_1(A_153, A_154))) | ~v1_finset_1(k10_relat_1(A_153, A_154)) | ~v1_funct_1(k7_relat_1(A_153, k10_relat_1(A_153, A_154))) | ~v1_relat_1(k7_relat_1(A_153, k10_relat_1(A_153, A_154))) | ~v1_relat_1(A_153) | ~r1_tarski(A_154, k2_relat_1(A_153)) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_164, c_274])).
% 3.64/1.63  tff(c_1038, plain, (![A_155, A_156]: (v1_finset_1(k9_relat_1(A_155, k10_relat_1(A_155, A_156))) | ~v1_finset_1(k10_relat_1(A_155, A_156)) | ~v1_funct_1(k7_relat_1(A_155, k10_relat_1(A_155, A_156))) | ~r1_tarski(A_156, k2_relat_1(A_155)) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_2, c_1026])).
% 3.64/1.63  tff(c_1084, plain, (![A_160, A_161]: (v1_finset_1(k9_relat_1(A_160, k10_relat_1(A_160, A_161))) | ~v1_finset_1(k10_relat_1(A_160, A_161)) | ~r1_tarski(A_161, k2_relat_1(A_160)) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_12, c_1038])).
% 3.64/1.63  tff(c_83, plain, (![A_5, A_34]: (r1_tarski(k10_relat_1(A_5, A_34), k1_relat_1(A_5)) | ~r1_tarski(A_34, k2_relat_1(A_5)) | ~v1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 3.64/1.63  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k10_relat_1(B_14, k9_relat_1(B_14, A_13))) | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.64/1.63  tff(c_166, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, B_54) | ~r1_tarski(A_53, k2_relat_1(C_55)) | ~r1_tarski(k10_relat_1(C_55, A_53), k10_relat_1(C_55, B_54)) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.64/1.63  tff(c_322, plain, (![A_84, B_85]: (r1_tarski(A_84, k9_relat_1(B_85, k10_relat_1(B_85, A_84))) | ~r1_tarski(A_84, k2_relat_1(B_85)) | ~v1_funct_1(B_85) | ~r1_tarski(k10_relat_1(B_85, A_84), k1_relat_1(B_85)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_16, c_166])).
% 3.64/1.63  tff(c_337, plain, (![A_88, A_89]: (r1_tarski(A_88, k9_relat_1(A_89, k10_relat_1(A_89, A_88))) | ~v1_funct_1(A_89) | ~r1_tarski(A_88, k2_relat_1(A_89)) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_83, c_322])).
% 3.64/1.63  tff(c_20, plain, (![A_18, B_19]: (v1_finset_1(A_18) | ~v1_finset_1(B_19) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.64/1.63  tff(c_355, plain, (![A_88, A_89]: (v1_finset_1(A_88) | ~v1_finset_1(k9_relat_1(A_89, k10_relat_1(A_89, A_88))) | ~v1_funct_1(A_89) | ~r1_tarski(A_88, k2_relat_1(A_89)) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_337, c_20])).
% 3.64/1.63  tff(c_1095, plain, (![A_162, A_163]: (v1_finset_1(A_162) | ~v1_finset_1(k10_relat_1(A_163, A_162)) | ~r1_tarski(A_162, k2_relat_1(A_163)) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_1084, c_355])).
% 3.64/1.63  tff(c_1101, plain, (v1_finset_1('#skF_1') | ~v1_finset_1(k10_relat_1('#skF_2', '#skF_1')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1095])).
% 3.64/1.63  tff(c_1104, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_1101])).
% 3.64/1.63  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1104])).
% 3.64/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.63  
% 3.64/1.63  Inference rules
% 3.64/1.63  ----------------------
% 3.64/1.63  #Ref     : 0
% 3.64/1.63  #Sup     : 284
% 3.64/1.63  #Fact    : 0
% 3.64/1.63  #Define  : 0
% 3.64/1.63  #Split   : 3
% 3.64/1.63  #Chain   : 0
% 3.64/1.63  #Close   : 0
% 3.64/1.63  
% 3.64/1.63  Ordering : KBO
% 3.64/1.63  
% 3.64/1.63  Simplification rules
% 3.64/1.63  ----------------------
% 3.64/1.63  #Subsume      : 50
% 3.64/1.63  #Demod        : 32
% 3.64/1.63  #Tautology    : 45
% 3.64/1.63  #SimpNegUnit  : 8
% 3.64/1.63  #BackRed      : 0
% 3.64/1.63  
% 3.64/1.63  #Partial instantiations: 0
% 3.64/1.63  #Strategies tried      : 1
% 3.64/1.63  
% 3.64/1.63  Timing (in seconds)
% 3.64/1.63  ----------------------
% 3.98/1.63  Preprocessing        : 0.29
% 3.98/1.63  Parsing              : 0.17
% 3.98/1.63  CNF conversion       : 0.02
% 3.98/1.63  Main loop            : 0.58
% 3.98/1.63  Inferencing          : 0.22
% 3.98/1.63  Reduction            : 0.14
% 3.98/1.63  Demodulation         : 0.09
% 3.98/1.63  BG Simplification    : 0.03
% 3.98/1.63  Subsumption          : 0.16
% 3.98/1.63  Abstraction          : 0.02
% 3.98/1.63  MUC search           : 0.00
% 3.98/1.63  Cooper               : 0.00
% 3.98/1.63  Total                : 0.90
% 3.98/1.63  Index Insertion      : 0.00
% 3.98/1.63  Index Deletion       : 0.00
% 3.98/1.63  Index Matching       : 0.00
% 3.98/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
