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
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   60 (  98 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 175 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [C_37,A_38,B_39] :
      ( k7_relat_1(k7_relat_1(C_37,A_38),B_39) = k7_relat_1(C_37,k3_xboole_0(A_38,B_39))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_927,plain,(
    ! [C_102,A_103,B_104] :
      ( k2_relat_1(k7_relat_1(C_102,k3_xboole_0(A_103,B_104))) = k9_relat_1(k7_relat_1(C_102,A_103),B_104)
      | ~ v1_relat_1(k7_relat_1(C_102,A_103))
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_14])).

tff(c_1069,plain,(
    ! [C_115,A_116,B_117] :
      ( k9_relat_1(k7_relat_1(C_115,A_116),B_117) = k9_relat_1(C_115,k3_xboole_0(A_116,B_117))
      | ~ v1_relat_1(C_115)
      | ~ v1_relat_1(k7_relat_1(C_115,A_116))
      | ~ v1_relat_1(C_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_14])).

tff(c_1077,plain,(
    ! [A_118,B_119,B_120] :
      ( k9_relat_1(k7_relat_1(A_118,B_119),B_120) = k9_relat_1(A_118,k3_xboole_0(B_119,B_120))
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_8,c_1069])).

tff(c_73,plain,(
    ! [B_32,A_33] :
      ( k2_relat_1(k7_relat_1(B_32,A_33)) = k9_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [B_32,A_33,A_14] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_32,A_33),A_14),k9_relat_1(B_32,A_33))
      | ~ v1_relat_1(k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_1181,plain,(
    ! [A_127,B_128,B_129] :
      ( r1_tarski(k9_relat_1(A_127,k3_xboole_0(B_128,B_129)),k9_relat_1(A_127,B_128))
      | ~ v1_relat_1(k7_relat_1(A_127,B_128))
      | ~ v1_relat_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_79])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_relat_1(k7_relat_1(C_50,k3_xboole_0(A_51,B_52))) = k9_relat_1(k7_relat_1(C_50,A_51),B_52)
      | ~ v1_relat_1(k7_relat_1(C_50,A_51))
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_14])).

tff(c_299,plain,(
    ! [C_62,A_63,B_64] :
      ( k9_relat_1(k7_relat_1(C_62,A_63),B_64) = k9_relat_1(C_62,k3_xboole_0(A_63,B_64))
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(k7_relat_1(C_62,A_63))
      | ~ v1_relat_1(C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_305,plain,(
    ! [A_65,B_66,B_67] :
      ( k9_relat_1(k7_relat_1(A_65,B_66),B_67) = k9_relat_1(A_65,k3_xboole_0(B_66,B_67))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_8,c_299])).

tff(c_404,plain,(
    ! [A_74,B_75,B_76] :
      ( r1_tarski(k9_relat_1(A_74,k3_xboole_0(B_75,B_76)),k9_relat_1(A_74,B_75))
      | ~ v1_relat_1(k7_relat_1(A_74,B_75))
      | ~ v1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_79])).

tff(c_434,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_tarski(k9_relat_1(A_77,k3_xboole_0(B_78,A_79)),k9_relat_1(A_77,A_79))
      | ~ v1_relat_1(k7_relat_1(A_77,A_79))
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_404])).

tff(c_125,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,k9_relat_1(B_41,k1_relat_1(B_41))) = k9_relat_1(B_41,k10_relat_1(B_41,A_40))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_3,A_40,B_41] :
      ( r1_tarski(A_3,A_40)
      | ~ r1_tarski(A_3,k9_relat_1(B_41,k10_relat_1(B_41,A_40)))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_4])).

tff(c_862,plain,(
    ! [A_99,B_100,A_101] :
      ( r1_tarski(k9_relat_1(A_99,k3_xboole_0(B_100,k10_relat_1(A_99,A_101))),A_101)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(k7_relat_1(A_99,k10_relat_1(A_99,A_101)))
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_434,c_137])).

tff(c_85,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,k3_xboole_0(B_35,C_36))
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_23,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_101,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_23])).

tff(c_207,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_869,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_862,c_207])).

tff(c_913,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_869])).

tff(c_920,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_913])).

tff(c_924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_920])).

tff(c_925,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1188,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1181,c_925])).

tff(c_1215,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1188])).

tff(c_1219,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1215])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.42/1.55  
% 3.42/1.55  %Foreground sorts:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Background operators:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Foreground operators:
% 3.42/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.42/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.42/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.42/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.55  
% 3.52/1.56  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 3.52/1.56  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.52/1.56  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.52/1.56  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.52/1.56  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.52/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.52/1.56  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 3.52/1.56  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.52/1.56  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.52/1.56  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.56  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.56  tff(c_104, plain, (![C_37, A_38, B_39]: (k7_relat_1(k7_relat_1(C_37, A_38), B_39)=k7_relat_1(C_37, k3_xboole_0(A_38, B_39)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.56  tff(c_14, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.56  tff(c_927, plain, (![C_102, A_103, B_104]: (k2_relat_1(k7_relat_1(C_102, k3_xboole_0(A_103, B_104)))=k9_relat_1(k7_relat_1(C_102, A_103), B_104) | ~v1_relat_1(k7_relat_1(C_102, A_103)) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_104, c_14])).
% 3.52/1.56  tff(c_1069, plain, (![C_115, A_116, B_117]: (k9_relat_1(k7_relat_1(C_115, A_116), B_117)=k9_relat_1(C_115, k3_xboole_0(A_116, B_117)) | ~v1_relat_1(C_115) | ~v1_relat_1(k7_relat_1(C_115, A_116)) | ~v1_relat_1(C_115))), inference(superposition, [status(thm), theory('equality')], [c_927, c_14])).
% 3.52/1.56  tff(c_1077, plain, (![A_118, B_119, B_120]: (k9_relat_1(k7_relat_1(A_118, B_119), B_120)=k9_relat_1(A_118, k3_xboole_0(B_119, B_120)) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_8, c_1069])).
% 3.52/1.56  tff(c_73, plain, (![B_32, A_33]: (k2_relat_1(k7_relat_1(B_32, A_33))=k9_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.56  tff(c_12, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.56  tff(c_79, plain, (![B_32, A_33, A_14]: (r1_tarski(k9_relat_1(k7_relat_1(B_32, A_33), A_14), k9_relat_1(B_32, A_33)) | ~v1_relat_1(k7_relat_1(B_32, A_33)) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_73, c_12])).
% 3.52/1.56  tff(c_1181, plain, (![A_127, B_128, B_129]: (r1_tarski(k9_relat_1(A_127, k3_xboole_0(B_128, B_129)), k9_relat_1(A_127, B_128)) | ~v1_relat_1(k7_relat_1(A_127, B_128)) | ~v1_relat_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_79])).
% 3.52/1.56  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.56  tff(c_208, plain, (![C_50, A_51, B_52]: (k2_relat_1(k7_relat_1(C_50, k3_xboole_0(A_51, B_52)))=k9_relat_1(k7_relat_1(C_50, A_51), B_52) | ~v1_relat_1(k7_relat_1(C_50, A_51)) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_104, c_14])).
% 3.52/1.56  tff(c_299, plain, (![C_62, A_63, B_64]: (k9_relat_1(k7_relat_1(C_62, A_63), B_64)=k9_relat_1(C_62, k3_xboole_0(A_63, B_64)) | ~v1_relat_1(C_62) | ~v1_relat_1(k7_relat_1(C_62, A_63)) | ~v1_relat_1(C_62))), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 3.52/1.56  tff(c_305, plain, (![A_65, B_66, B_67]: (k9_relat_1(k7_relat_1(A_65, B_66), B_67)=k9_relat_1(A_65, k3_xboole_0(B_66, B_67)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_8, c_299])).
% 3.52/1.56  tff(c_404, plain, (![A_74, B_75, B_76]: (r1_tarski(k9_relat_1(A_74, k3_xboole_0(B_75, B_76)), k9_relat_1(A_74, B_75)) | ~v1_relat_1(k7_relat_1(A_74, B_75)) | ~v1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_305, c_79])).
% 3.52/1.56  tff(c_434, plain, (![A_77, B_78, A_79]: (r1_tarski(k9_relat_1(A_77, k3_xboole_0(B_78, A_79)), k9_relat_1(A_77, A_79)) | ~v1_relat_1(k7_relat_1(A_77, A_79)) | ~v1_relat_1(A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_2, c_404])).
% 3.52/1.56  tff(c_125, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k9_relat_1(B_41, k1_relat_1(B_41)))=k9_relat_1(B_41, k10_relat_1(B_41, A_40)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.56  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.56  tff(c_137, plain, (![A_3, A_40, B_41]: (r1_tarski(A_3, A_40) | ~r1_tarski(A_3, k9_relat_1(B_41, k10_relat_1(B_41, A_40))) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_125, c_4])).
% 3.52/1.56  tff(c_862, plain, (![A_99, B_100, A_101]: (r1_tarski(k9_relat_1(A_99, k3_xboole_0(B_100, k10_relat_1(A_99, A_101))), A_101) | ~v1_funct_1(A_99) | ~v1_relat_1(k7_relat_1(A_99, k10_relat_1(A_99, A_101))) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_434, c_137])).
% 3.52/1.56  tff(c_85, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, k3_xboole_0(B_35, C_36)) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.56  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.56  tff(c_23, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 3.52/1.56  tff(c_101, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_85, c_23])).
% 3.52/1.56  tff(c_207, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_101])).
% 3.52/1.56  tff(c_869, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_862, c_207])).
% 3.52/1.56  tff(c_913, plain, (~v1_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_869])).
% 3.52/1.56  tff(c_920, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_913])).
% 3.52/1.56  tff(c_924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_920])).
% 3.52/1.56  tff(c_925, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_101])).
% 3.52/1.56  tff(c_1188, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1181, c_925])).
% 3.52/1.56  tff(c_1215, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1188])).
% 3.52/1.56  tff(c_1219, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1215])).
% 3.52/1.56  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1219])).
% 3.52/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  Inference rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Ref     : 0
% 3.52/1.56  #Sup     : 323
% 3.52/1.56  #Fact    : 0
% 3.52/1.56  #Define  : 0
% 3.52/1.56  #Split   : 1
% 3.52/1.56  #Chain   : 0
% 3.52/1.56  #Close   : 0
% 3.52/1.56  
% 3.52/1.56  Ordering : KBO
% 3.52/1.56  
% 3.52/1.56  Simplification rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Subsume      : 62
% 3.52/1.56  #Demod        : 13
% 3.52/1.56  #Tautology    : 50
% 3.52/1.56  #SimpNegUnit  : 0
% 3.52/1.56  #BackRed      : 0
% 3.52/1.56  
% 3.52/1.56  #Partial instantiations: 0
% 3.52/1.56  #Strategies tried      : 1
% 3.52/1.56  
% 3.52/1.56  Timing (in seconds)
% 3.52/1.56  ----------------------
% 3.52/1.56  Preprocessing        : 0.29
% 3.52/1.56  Parsing              : 0.16
% 3.52/1.56  CNF conversion       : 0.02
% 3.52/1.57  Main loop            : 0.51
% 3.52/1.57  Inferencing          : 0.20
% 3.52/1.57  Reduction            : 0.15
% 3.52/1.57  Demodulation         : 0.11
% 3.52/1.57  BG Simplification    : 0.03
% 3.52/1.57  Subsumption          : 0.10
% 3.52/1.57  Abstraction          : 0.03
% 3.52/1.57  MUC search           : 0.00
% 3.52/1.57  Cooper               : 0.00
% 3.52/1.57  Total                : 0.83
% 3.52/1.57  Index Insertion      : 0.00
% 3.52/1.57  Index Deletion       : 0.00
% 3.52/1.57  Index Matching       : 0.00
% 3.52/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
