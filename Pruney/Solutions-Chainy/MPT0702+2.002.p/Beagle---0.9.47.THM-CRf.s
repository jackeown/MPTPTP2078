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
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 191 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_154,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_162,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_30])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_592,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k10_relat_1(B_58,k9_relat_1(B_58,A_59)),A_59)
      | ~ v2_funct_1(B_58)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4026,plain,(
    ! [B_124,A_125] :
      ( k10_relat_1(B_124,k9_relat_1(B_124,A_125)) = A_125
      | ~ r1_tarski(A_125,k10_relat_1(B_124,k9_relat_1(B_124,A_125)))
      | ~ v2_funct_1(B_124)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_592,c_2])).

tff(c_5985,plain,(
    ! [B_147,A_148] :
      ( k10_relat_1(B_147,k9_relat_1(B_147,A_148)) = A_148
      | ~ v2_funct_1(B_147)
      | ~ v1_funct_1(B_147)
      | ~ r1_tarski(A_148,k1_relat_1(B_147))
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_26,c_4026])).

tff(c_6004,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_5985])).

tff(c_6018,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_6004])).

tff(c_1116,plain,(
    ! [C_72,A_73,B_74] :
      ( k3_xboole_0(k9_relat_1(C_72,A_73),k9_relat_1(C_72,B_74)) = k9_relat_1(C_72,k3_xboole_0(A_73,B_74))
      | ~ v2_funct_1(C_72)
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_101,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_425,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_451,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_425])).

tff(c_469,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_451])).

tff(c_1125,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_469])).

tff(c_1181,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_1125])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1201,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1181,c_28])).

tff(c_1211,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_1201])).

tff(c_6021,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_1211])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_362,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k3_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_12,c_346])).

tff(c_6076,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6021,c_362])).

tff(c_18,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(B_40,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_22,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_206,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_22])).

tff(c_115,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_229,plain,(
    ! [B_41,A_42] : k4_xboole_0(k3_xboole_0(B_41,A_42),A_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_115])).

tff(c_6181,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6076,c_229])).

tff(c_6227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_6181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:40:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.32  
% 5.87/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.32  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.87/2.32  
% 5.87/2.32  %Foreground sorts:
% 5.87/2.32  
% 5.87/2.32  
% 5.87/2.32  %Background operators:
% 5.87/2.32  
% 5.87/2.32  
% 5.87/2.32  %Foreground operators:
% 5.87/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.87/2.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.87/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.87/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.87/2.32  tff('#skF_2', type, '#skF_2': $i).
% 5.87/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.87/2.32  tff('#skF_3', type, '#skF_3': $i).
% 5.87/2.32  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.87/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.87/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.87/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.87/2.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.87/2.32  
% 5.87/2.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.87/2.34  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 5.87/2.34  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.87/2.34  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 5.87/2.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.87/2.34  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 5.87/2.34  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.87/2.34  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.87/2.34  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.87/2.34  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.87/2.34  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.87/2.34  tff(c_154, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.34  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_162, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_30])).
% 5.87/2.34  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.34  tff(c_592, plain, (![B_58, A_59]: (r1_tarski(k10_relat_1(B_58, k9_relat_1(B_58, A_59)), A_59) | ~v2_funct_1(B_58) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.87/2.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.87/2.34  tff(c_4026, plain, (![B_124, A_125]: (k10_relat_1(B_124, k9_relat_1(B_124, A_125))=A_125 | ~r1_tarski(A_125, k10_relat_1(B_124, k9_relat_1(B_124, A_125))) | ~v2_funct_1(B_124) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_592, c_2])).
% 5.87/2.34  tff(c_5985, plain, (![B_147, A_148]: (k10_relat_1(B_147, k9_relat_1(B_147, A_148))=A_148 | ~v2_funct_1(B_147) | ~v1_funct_1(B_147) | ~r1_tarski(A_148, k1_relat_1(B_147)) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_26, c_4026])).
% 5.87/2.34  tff(c_6004, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_5985])).
% 5.87/2.34  tff(c_6018, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_6004])).
% 5.87/2.34  tff(c_1116, plain, (![C_72, A_73, B_74]: (k3_xboole_0(k9_relat_1(C_72, A_73), k9_relat_1(C_72, B_74))=k9_relat_1(C_72, k3_xboole_0(A_73, B_74)) | ~v2_funct_1(C_72) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.87/2.34  tff(c_14, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.34  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.34  tff(c_101, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.34  tff(c_114, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_101])).
% 5.87/2.34  tff(c_425, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.87/2.34  tff(c_451, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_425])).
% 5.87/2.34  tff(c_469, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_451])).
% 5.87/2.34  tff(c_1125, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1116, c_469])).
% 5.87/2.34  tff(c_1181, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_1125])).
% 5.87/2.34  tff(c_28, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.87/2.34  tff(c_1201, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1181, c_28])).
% 5.87/2.34  tff(c_1211, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_1201])).
% 5.87/2.34  tff(c_6021, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6018, c_1211])).
% 5.87/2.34  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.87/2.34  tff(c_346, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.87/2.34  tff(c_362, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_12, c_346])).
% 5.87/2.34  tff(c_6076, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_6021, c_362])).
% 5.87/2.34  tff(c_18, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.87/2.34  tff(c_86, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.87/2.34  tff(c_183, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(B_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_18, c_86])).
% 5.87/2.34  tff(c_22, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.87/2.34  tff(c_206, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_183, c_22])).
% 5.87/2.34  tff(c_115, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_101])).
% 5.87/2.34  tff(c_229, plain, (![B_41, A_42]: (k4_xboole_0(k3_xboole_0(B_41, A_42), A_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_115])).
% 5.87/2.34  tff(c_6181, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6076, c_229])).
% 5.87/2.34  tff(c_6227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_6181])).
% 5.87/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.34  
% 5.87/2.34  Inference rules
% 5.87/2.34  ----------------------
% 5.87/2.34  #Ref     : 0
% 5.87/2.34  #Sup     : 1521
% 5.87/2.34  #Fact    : 0
% 5.87/2.34  #Define  : 0
% 5.87/2.34  #Split   : 4
% 5.87/2.34  #Chain   : 0
% 5.87/2.34  #Close   : 0
% 5.87/2.34  
% 5.87/2.34  Ordering : KBO
% 5.87/2.34  
% 5.87/2.34  Simplification rules
% 5.87/2.34  ----------------------
% 5.87/2.34  #Subsume      : 274
% 5.87/2.34  #Demod        : 2300
% 5.87/2.34  #Tautology    : 979
% 5.87/2.34  #SimpNegUnit  : 10
% 5.87/2.34  #BackRed      : 4
% 5.87/2.34  
% 5.87/2.34  #Partial instantiations: 0
% 5.87/2.34  #Strategies tried      : 1
% 5.87/2.34  
% 5.87/2.34  Timing (in seconds)
% 5.87/2.34  ----------------------
% 5.87/2.35  Preprocessing        : 0.32
% 5.87/2.35  Parsing              : 0.17
% 5.87/2.35  CNF conversion       : 0.02
% 5.87/2.35  Main loop            : 1.26
% 5.87/2.35  Inferencing          : 0.35
% 5.87/2.35  Reduction            : 0.62
% 5.87/2.35  Demodulation         : 0.52
% 5.87/2.35  BG Simplification    : 0.03
% 6.10/2.35  Subsumption          : 0.19
% 6.10/2.35  Abstraction          : 0.06
% 6.10/2.35  MUC search           : 0.00
% 6.10/2.35  Cooper               : 0.00
% 6.10/2.35  Total                : 1.61
% 6.10/2.35  Index Insertion      : 0.00
% 6.10/2.35  Index Deletion       : 0.00
% 6.10/2.35  Index Matching       : 0.00
% 6.10/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
