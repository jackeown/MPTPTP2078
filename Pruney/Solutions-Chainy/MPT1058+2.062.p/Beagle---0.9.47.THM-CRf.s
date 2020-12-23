%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 149 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 248 expanded)
%              Number of equality atoms :   31 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_36,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_251,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_260,plain,(
    ! [A_14,A_59] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_59)) = k3_xboole_0(A_14,A_59)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_251])).

tff(c_264,plain,(
    ! [A_14,A_59] : k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_59)) = k3_xboole_0(A_14,A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_260])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_615,plain,(
    ! [A_88,B_89] :
      ( k10_relat_1(A_88,k1_relat_1(B_89)) = k1_relat_1(k5_relat_1(A_88,B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_702,plain,(
    ! [A_88,A_14] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_14))) = k10_relat_1(A_88,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_615])).

tff(c_768,plain,(
    ! [A_92,A_93] :
      ( k1_relat_1(k5_relat_1(A_92,k6_relat_1(A_93))) = k10_relat_1(A_92,A_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_702])).

tff(c_794,plain,(
    ! [A_93,A_17] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_93),A_17)) = k10_relat_1(k6_relat_1(A_17),A_93)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_768])).

tff(c_800,plain,(
    ! [A_17,A_93] : k10_relat_1(k6_relat_1(A_17),A_93) = k3_xboole_0(A_93,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_264,c_794])).

tff(c_20,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [A_37] :
      ( k10_relat_1(A_37,k2_relat_1(A_37)) = k1_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    ! [A_14] :
      ( k10_relat_1(k6_relat_1(A_14),A_14) = k1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_87,plain,(
    ! [A_14] : k10_relat_1(k6_relat_1(A_14),A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18,c_83])).

tff(c_280,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k9_relat_1(B_62,k10_relat_1(B_62,A_63)),A_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_295,plain,(
    ! [A_14] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_14),A_14),A_14)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_280])).

tff(c_305,plain,(
    ! [A_64] : r1_tarski(k9_relat_1(k6_relat_1(A_64),A_64),A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_295])).

tff(c_38,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_139,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_2')
      | ~ r1_tarski(A_45,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_139])).

tff(c_319,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_305,c_150])).

tff(c_901,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(A_97,k10_relat_1(C_98,B_99))
      | ~ r1_tarski(k9_relat_1(C_98,A_97),B_99)
      | ~ r1_tarski(A_97,k1_relat_1(C_98))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_907,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_319,c_901])).

tff(c_921,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_6,c_18,c_800,c_907])).

tff(c_107,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k10_relat_1(B_41,A_42),k1_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_14,A_42] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_14),A_42),A_14)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_125,plain,(
    ! [A_43,A_44] : r1_tarski(k10_relat_1(k6_relat_1(A_43),A_44),A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_43,A_44] :
      ( k10_relat_1(k6_relat_1(A_43),A_44) = A_43
      | ~ r1_tarski(A_43,k10_relat_1(k6_relat_1(A_43),A_44)) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_804,plain,(
    ! [A_44,A_43] :
      ( k3_xboole_0(A_44,A_43) = A_43
      | ~ r1_tarski(A_43,k3_xboole_0(A_44,A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_800,c_135])).

tff(c_1342,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_921,c_804])).

tff(c_30,plain,(
    ! [A_20,C_22,B_21] :
      ( k3_xboole_0(A_20,k10_relat_1(C_22,B_21)) = k10_relat_1(k7_relat_1(C_22,A_20),B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1375,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_30])).

tff(c_1389,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1375])).

tff(c_1391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.50  
% 3.26/1.50  %Foreground sorts:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Background operators:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Foreground operators:
% 3.26/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.50  
% 3.39/1.52  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.39/1.52  tff(f_70, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.39/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.52  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.39/1.52  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.39/1.52  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.39/1.52  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.39/1.52  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.39/1.52  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.39/1.52  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.39/1.52  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.39/1.52  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.39/1.52  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.39/1.52  tff(c_36, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.39/1.52  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.39/1.52  tff(c_26, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.39/1.52  tff(c_28, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.39/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.52  tff(c_18, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.52  tff(c_251, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.52  tff(c_260, plain, (![A_14, A_59]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_59))=k3_xboole_0(A_14, A_59) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_251])).
% 3.39/1.52  tff(c_264, plain, (![A_14, A_59]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_59))=k3_xboole_0(A_14, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_260])).
% 3.39/1.52  tff(c_24, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.39/1.52  tff(c_615, plain, (![A_88, B_89]: (k10_relat_1(A_88, k1_relat_1(B_89))=k1_relat_1(k5_relat_1(A_88, B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.52  tff(c_702, plain, (![A_88, A_14]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_14)))=k10_relat_1(A_88, A_14) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_18, c_615])).
% 3.39/1.52  tff(c_768, plain, (![A_92, A_93]: (k1_relat_1(k5_relat_1(A_92, k6_relat_1(A_93)))=k10_relat_1(A_92, A_93) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_702])).
% 3.39/1.52  tff(c_794, plain, (![A_93, A_17]: (k1_relat_1(k7_relat_1(k6_relat_1(A_93), A_17))=k10_relat_1(k6_relat_1(A_17), A_93) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_768])).
% 3.39/1.52  tff(c_800, plain, (![A_17, A_93]: (k10_relat_1(k6_relat_1(A_17), A_93)=k3_xboole_0(A_93, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_264, c_794])).
% 3.39/1.52  tff(c_20, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.52  tff(c_74, plain, (![A_37]: (k10_relat_1(A_37, k2_relat_1(A_37))=k1_relat_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.52  tff(c_83, plain, (![A_14]: (k10_relat_1(k6_relat_1(A_14), A_14)=k1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_74])).
% 3.39/1.52  tff(c_87, plain, (![A_14]: (k10_relat_1(k6_relat_1(A_14), A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18, c_83])).
% 3.39/1.52  tff(c_280, plain, (![B_62, A_63]: (r1_tarski(k9_relat_1(B_62, k10_relat_1(B_62, A_63)), A_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.52  tff(c_295, plain, (![A_14]: (r1_tarski(k9_relat_1(k6_relat_1(A_14), A_14), A_14) | ~v1_funct_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_280])).
% 3.39/1.52  tff(c_305, plain, (![A_64]: (r1_tarski(k9_relat_1(k6_relat_1(A_64), A_64), A_64))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_295])).
% 3.39/1.52  tff(c_38, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.39/1.52  tff(c_139, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.52  tff(c_150, plain, (![A_45]: (r1_tarski(A_45, '#skF_2') | ~r1_tarski(A_45, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_38, c_139])).
% 3.39/1.52  tff(c_319, plain, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_305, c_150])).
% 3.39/1.52  tff(c_901, plain, (![A_97, C_98, B_99]: (r1_tarski(A_97, k10_relat_1(C_98, B_99)) | ~r1_tarski(k9_relat_1(C_98, A_97), B_99) | ~r1_tarski(A_97, k1_relat_1(C_98)) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.52  tff(c_907, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_319, c_901])).
% 3.39/1.52  tff(c_921, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_6, c_18, c_800, c_907])).
% 3.39/1.52  tff(c_107, plain, (![B_41, A_42]: (r1_tarski(k10_relat_1(B_41, A_42), k1_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.52  tff(c_118, plain, (![A_14, A_42]: (r1_tarski(k10_relat_1(k6_relat_1(A_14), A_42), A_14) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_107])).
% 3.39/1.52  tff(c_125, plain, (![A_43, A_44]: (r1_tarski(k10_relat_1(k6_relat_1(A_43), A_44), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_118])).
% 3.39/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.52  tff(c_135, plain, (![A_43, A_44]: (k10_relat_1(k6_relat_1(A_43), A_44)=A_43 | ~r1_tarski(A_43, k10_relat_1(k6_relat_1(A_43), A_44)))), inference(resolution, [status(thm)], [c_125, c_2])).
% 3.39/1.52  tff(c_804, plain, (![A_44, A_43]: (k3_xboole_0(A_44, A_43)=A_43 | ~r1_tarski(A_43, k3_xboole_0(A_44, A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_800, c_135])).
% 3.39/1.52  tff(c_1342, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_921, c_804])).
% 3.39/1.52  tff(c_30, plain, (![A_20, C_22, B_21]: (k3_xboole_0(A_20, k10_relat_1(C_22, B_21))=k10_relat_1(k7_relat_1(C_22, A_20), B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.52  tff(c_1375, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1342, c_30])).
% 3.39/1.52  tff(c_1389, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1375])).
% 3.39/1.52  tff(c_1391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1389])).
% 3.39/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.52  
% 3.39/1.52  Inference rules
% 3.39/1.52  ----------------------
% 3.39/1.52  #Ref     : 0
% 3.39/1.52  #Sup     : 296
% 3.39/1.52  #Fact    : 0
% 3.39/1.52  #Define  : 0
% 3.39/1.52  #Split   : 1
% 3.39/1.52  #Chain   : 0
% 3.39/1.52  #Close   : 0
% 3.39/1.52  
% 3.39/1.52  Ordering : KBO
% 3.39/1.52  
% 3.39/1.52  Simplification rules
% 3.39/1.52  ----------------------
% 3.39/1.52  #Subsume      : 11
% 3.39/1.52  #Demod        : 202
% 3.39/1.52  #Tautology    : 99
% 3.39/1.52  #SimpNegUnit  : 1
% 3.39/1.52  #BackRed      : 10
% 3.39/1.52  
% 3.39/1.52  #Partial instantiations: 0
% 3.39/1.52  #Strategies tried      : 1
% 3.39/1.52  
% 3.39/1.52  Timing (in seconds)
% 3.39/1.52  ----------------------
% 3.39/1.52  Preprocessing        : 0.31
% 3.39/1.52  Parsing              : 0.16
% 3.39/1.52  CNF conversion       : 0.02
% 3.39/1.52  Main loop            : 0.44
% 3.39/1.52  Inferencing          : 0.15
% 3.39/1.52  Reduction            : 0.15
% 3.39/1.52  Demodulation         : 0.11
% 3.39/1.52  BG Simplification    : 0.02
% 3.39/1.52  Subsumption          : 0.08
% 3.39/1.53  Abstraction          : 0.03
% 3.39/1.53  MUC search           : 0.00
% 3.39/1.53  Cooper               : 0.00
% 3.39/1.53  Total                : 0.78
% 3.39/1.53  Index Insertion      : 0.00
% 3.39/1.53  Index Deletion       : 0.00
% 3.39/1.53  Index Matching       : 0.00
% 3.39/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
