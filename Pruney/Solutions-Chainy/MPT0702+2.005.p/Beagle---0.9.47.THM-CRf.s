%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 294 expanded)
%              Number of leaves         :   26 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 827 expanded)
%              Number of equality atoms :   30 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,k10_relat_1(B_17,k9_relat_1(B_17,A_16)))
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_671,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k10_relat_1(B_52,k9_relat_1(B_52,A_53)),A_53)
      | ~ v2_funct_1(B_52)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2774,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(B_86,k9_relat_1(B_86,A_87)) = A_87
      | ~ r1_tarski(A_87,k10_relat_1(B_86,k9_relat_1(B_86,A_87)))
      | ~ v2_funct_1(B_86)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_671,c_2])).

tff(c_3053,plain,(
    ! [B_93,A_94] :
      ( k10_relat_1(B_93,k9_relat_1(B_93,A_94)) = A_94
      | ~ v2_funct_1(B_93)
      | ~ v1_funct_1(B_93)
      | ~ r1_tarski(A_94,k1_relat_1(B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_20,c_2774])).

tff(c_3064,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_3053])).

tff(c_3073,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_3064])).

tff(c_1058,plain,(
    ! [C_60,A_61,B_62] :
      ( k3_xboole_0(k9_relat_1(C_60,A_61),k9_relat_1(C_60,B_62)) = k9_relat_1(C_60,k3_xboole_0(A_61,B_62))
      | ~ v2_funct_1(C_60)
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_1082,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_84])).

tff(c_1129,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1082])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,k9_relat_1(B_19,A_18)),A_18)
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1145,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_22])).

tff(c_1156,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1145])).

tff(c_3075,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3073,c_1156])).

tff(c_186,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_3117,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3075,c_196])).

tff(c_338,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,k10_relat_1(B_45,k9_relat_1(B_45,A_44)))
      | ~ r1_tarski(A_44,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2805,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(B_89,k9_relat_1(B_89,A_90)) = A_90
      | ~ r1_tarski(k10_relat_1(B_89,k9_relat_1(B_89,A_90)),A_90)
      | ~ r1_tarski(A_90,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_2811,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_2805])).

tff(c_2818,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1156,c_1129,c_2811])).

tff(c_2913,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2818])).

tff(c_3124,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3117,c_2913])).

tff(c_3130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3124])).

tff(c_3131,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2818])).

tff(c_344,plain,(
    ! [B_45,A_44] :
      ( k10_relat_1(B_45,k9_relat_1(B_45,A_44)) = A_44
      | ~ r1_tarski(k10_relat_1(B_45,k9_relat_1(B_45,A_44)),A_44)
      | ~ r1_tarski(A_44,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_3284,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3131,c_344])).

tff(c_3300,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_8,c_3131,c_3284])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_16,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_16])).

tff(c_162,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_8])).

tff(c_3382,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3300,c_162])).

tff(c_3412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:10:27 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.78  
% 4.01/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.78  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.01/1.78  
% 4.01/1.78  %Foreground sorts:
% 4.01/1.78  
% 4.01/1.78  
% 4.01/1.78  %Background operators:
% 4.01/1.78  
% 4.01/1.78  
% 4.01/1.78  %Foreground operators:
% 4.01/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.01/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.01/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.01/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.01/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.01/1.78  
% 4.40/1.80  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.40/1.80  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.40/1.80  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.40/1.80  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.40/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.40/1.80  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 4.40/1.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.40/1.80  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.40/1.80  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.40/1.80  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.40/1.80  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k10_relat_1(B_17, k9_relat_1(B_17, A_16))) | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.80  tff(c_671, plain, (![B_52, A_53]: (r1_tarski(k10_relat_1(B_52, k9_relat_1(B_52, A_53)), A_53) | ~v2_funct_1(B_52) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.40/1.80  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.80  tff(c_2774, plain, (![B_86, A_87]: (k10_relat_1(B_86, k9_relat_1(B_86, A_87))=A_87 | ~r1_tarski(A_87, k10_relat_1(B_86, k9_relat_1(B_86, A_87))) | ~v2_funct_1(B_86) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_671, c_2])).
% 4.40/1.80  tff(c_3053, plain, (![B_93, A_94]: (k10_relat_1(B_93, k9_relat_1(B_93, A_94))=A_94 | ~v2_funct_1(B_93) | ~v1_funct_1(B_93) | ~r1_tarski(A_94, k1_relat_1(B_93)) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_20, c_2774])).
% 4.40/1.80  tff(c_3064, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_3053])).
% 4.40/1.80  tff(c_3073, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_3064])).
% 4.40/1.80  tff(c_1058, plain, (![C_60, A_61, B_62]: (k3_xboole_0(k9_relat_1(C_60, A_61), k9_relat_1(C_60, B_62))=k9_relat_1(C_60, k3_xboole_0(A_61, B_62)) | ~v2_funct_1(C_60) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.40/1.80  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_71, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.40/1.80  tff(c_84, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_71])).
% 4.40/1.80  tff(c_1082, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1058, c_84])).
% 4.40/1.80  tff(c_1129, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1082])).
% 4.40/1.80  tff(c_22, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, k9_relat_1(B_19, A_18)), A_18) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.40/1.80  tff(c_1145, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_22])).
% 4.40/1.80  tff(c_1156, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1145])).
% 4.40/1.80  tff(c_3075, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3073, c_1156])).
% 4.40/1.80  tff(c_186, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.80  tff(c_196, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_186])).
% 4.40/1.80  tff(c_3117, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_3075, c_196])).
% 4.40/1.80  tff(c_338, plain, (![A_44, B_45]: (r1_tarski(A_44, k10_relat_1(B_45, k9_relat_1(B_45, A_44))) | ~r1_tarski(A_44, k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.80  tff(c_2805, plain, (![B_89, A_90]: (k10_relat_1(B_89, k9_relat_1(B_89, A_90))=A_90 | ~r1_tarski(k10_relat_1(B_89, k9_relat_1(B_89, A_90)), A_90) | ~r1_tarski(A_90, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_338, c_2])).
% 4.40/1.80  tff(c_2811, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_2805])).
% 4.40/1.80  tff(c_2818, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1156, c_1129, c_2811])).
% 4.40/1.80  tff(c_2913, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2818])).
% 4.40/1.80  tff(c_3124, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3117, c_2913])).
% 4.40/1.80  tff(c_3130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3124])).
% 4.40/1.80  tff(c_3131, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2818])).
% 4.40/1.80  tff(c_344, plain, (![B_45, A_44]: (k10_relat_1(B_45, k9_relat_1(B_45, A_44))=A_44 | ~r1_tarski(k10_relat_1(B_45, k9_relat_1(B_45, A_44)), A_44) | ~r1_tarski(A_44, k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_338, c_2])).
% 4.40/1.80  tff(c_3284, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3131, c_344])).
% 4.40/1.80  tff(c_3300, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_8, c_3131, c_3284])).
% 4.40/1.80  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.40/1.80  tff(c_109, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.40/1.80  tff(c_124, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_12, c_109])).
% 4.40/1.80  tff(c_16, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.40/1.80  tff(c_147, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_124, c_16])).
% 4.40/1.80  tff(c_162, plain, (![B_32, A_33]: (r1_tarski(k3_xboole_0(B_32, A_33), A_33))), inference(superposition, [status(thm), theory('equality')], [c_147, c_8])).
% 4.40/1.80  tff(c_3382, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3300, c_162])).
% 4.40/1.80  tff(c_3412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_3382])).
% 4.40/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.80  
% 4.40/1.80  Inference rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Ref     : 0
% 4.40/1.80  #Sup     : 802
% 4.40/1.80  #Fact    : 0
% 4.40/1.80  #Define  : 0
% 4.40/1.80  #Split   : 3
% 4.40/1.80  #Chain   : 0
% 4.40/1.80  #Close   : 0
% 4.40/1.80  
% 4.40/1.80  Ordering : KBO
% 4.40/1.80  
% 4.40/1.80  Simplification rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Subsume      : 102
% 4.40/1.80  #Demod        : 1363
% 4.40/1.80  #Tautology    : 561
% 4.40/1.80  #SimpNegUnit  : 1
% 4.40/1.80  #BackRed      : 12
% 4.40/1.80  
% 4.40/1.80  #Partial instantiations: 0
% 4.40/1.80  #Strategies tried      : 1
% 4.40/1.80  
% 4.40/1.80  Timing (in seconds)
% 4.40/1.80  ----------------------
% 4.40/1.80  Preprocessing        : 0.30
% 4.40/1.80  Parsing              : 0.16
% 4.40/1.80  CNF conversion       : 0.02
% 4.40/1.80  Main loop            : 0.70
% 4.40/1.80  Inferencing          : 0.19
% 4.40/1.80  Reduction            : 0.35
% 4.40/1.80  Demodulation         : 0.30
% 4.40/1.80  BG Simplification    : 0.02
% 4.40/1.80  Subsumption          : 0.11
% 4.40/1.80  Abstraction          : 0.04
% 4.40/1.80  MUC search           : 0.00
% 4.40/1.80  Cooper               : 0.00
% 4.40/1.80  Total                : 1.03
% 4.40/1.80  Index Insertion      : 0.00
% 4.40/1.80  Index Deletion       : 0.00
% 4.40/1.80  Index Matching       : 0.00
% 4.40/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
