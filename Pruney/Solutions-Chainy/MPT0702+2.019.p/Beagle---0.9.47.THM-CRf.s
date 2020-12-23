%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 128 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 265 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k9_relat_1(k2_funct_1(B_23),A_22) = k10_relat_1(B_23,A_22)
      | ~ v2_funct_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_31] :
      ( v1_relat_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1380,plain,(
    ! [A_98] :
      ( k9_relat_1(k2_funct_1(A_98),k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_68,c_22])).

tff(c_13351,plain,(
    ! [B_298] :
      ( k10_relat_1(B_298,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(B_298)
      | ~ v1_relat_1(B_298)
      | ~ v2_funct_1(B_298)
      | ~ v1_funct_1(B_298)
      | ~ v1_relat_1(B_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1380])).

tff(c_13354,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_13351])).

tff(c_13357,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_13354])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_34])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_325,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(resolution,[status(thm)],[c_6,c_325])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_468,plain,(
    ! [A_62,B_63,B_64] : r1_tarski(A_62,k2_xboole_0(k2_xboole_0(A_62,B_63),B_64)) ),
    inference(resolution,[status(thm)],[c_349,c_12])).

tff(c_526,plain,(
    ! [A_65,B_66,B_67] : r1_tarski(k4_xboole_0(A_65,B_66),k2_xboole_0(A_65,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_468])).

tff(c_558,plain,(
    ! [B_66] : r1_tarski(k4_xboole_0('#skF_1',B_66),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_526])).

tff(c_20,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [C_19,A_17,B_18] :
      ( k6_subset_1(k9_relat_1(C_19,A_17),k9_relat_1(C_19,B_18)) = k9_relat_1(C_19,k6_subset_1(A_17,B_18))
      | ~ v2_funct_1(C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1119,plain,(
    ! [C_91,A_92,B_93] :
      ( k4_xboole_0(k9_relat_1(C_91,A_92),k9_relat_1(C_91,B_93)) = k9_relat_1(C_91,k4_xboole_0(A_92,B_93))
      | ~ v2_funct_1(C_91)
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_28])).

tff(c_40,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_165,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_145])).

tff(c_1137,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_165])).

tff(c_1175,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_1137])).

tff(c_733,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,k10_relat_1(B_75,k9_relat_1(B_75,A_74)))
      | ~ r1_tarski(A_74,k1_relat_1(B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5262,plain,(
    ! [A_184,B_185] :
      ( k2_xboole_0(A_184,k10_relat_1(B_185,k9_relat_1(B_185,A_184))) = k10_relat_1(B_185,k9_relat_1(B_185,A_184))
      | ~ r1_tarski(A_184,k1_relat_1(B_185))
      | ~ v1_relat_1(B_185) ) ),
    inference(resolution,[status(thm)],[c_733,c_14])).

tff(c_5405,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k10_relat_1('#skF_3',k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_5262])).

tff(c_5433,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k10_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_558,c_1175,c_5405])).

tff(c_8821,plain,(
    ! [C_244] :
      ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),C_244)
      | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),C_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5433,c_12])).

tff(c_220,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_8838,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8821,c_237])).

tff(c_8853,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_8838])).

tff(c_8860,plain,(
    k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_8853])).

tff(c_13361,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13357,c_8860])).

tff(c_13372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_13361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:27:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.84  
% 7.61/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.85  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.61/2.85  
% 7.61/2.85  %Foreground sorts:
% 7.61/2.85  
% 7.61/2.85  
% 7.61/2.85  %Background operators:
% 7.61/2.85  
% 7.61/2.85  
% 7.61/2.85  %Foreground operators:
% 7.61/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.61/2.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.61/2.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.61/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.61/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.61/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.61/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.61/2.85  tff('#skF_2', type, '#skF_2': $i).
% 7.61/2.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.61/2.85  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.61/2.85  tff('#skF_3', type, '#skF_3': $i).
% 7.61/2.85  tff('#skF_1', type, '#skF_1': $i).
% 7.61/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.61/2.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.61/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.61/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.61/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.61/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.61/2.85  
% 7.87/2.86  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.87/2.86  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.87/2.86  tff(f_96, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 7.87/2.86  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 7.87/2.86  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.87/2.86  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 7.87/2.86  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.87/2.86  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.87/2.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.87/2.86  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.87/2.86  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.87/2.86  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 7.87/2.86  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 7.87/2.86  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.87/2.86  tff(c_145, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.87/2.86  tff(c_168, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_145])).
% 7.87/2.86  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_36, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_32, plain, (![B_23, A_22]: (k9_relat_1(k2_funct_1(B_23), A_22)=k10_relat_1(B_23, A_22) | ~v2_funct_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.87/2.86  tff(c_68, plain, (![A_31]: (v1_relat_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.87/2.86  tff(c_22, plain, (![A_15]: (k9_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.87/2.86  tff(c_1380, plain, (![A_98]: (k9_relat_1(k2_funct_1(A_98), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_68, c_22])).
% 7.87/2.86  tff(c_13351, plain, (![B_298]: (k10_relat_1(B_298, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(B_298) | ~v1_relat_1(B_298) | ~v2_funct_1(B_298) | ~v1_funct_1(B_298) | ~v1_relat_1(B_298))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1380])).
% 7.87/2.86  tff(c_13354, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_13351])).
% 7.87/2.86  tff(c_13357, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_13354])).
% 7.87/2.86  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.87/2.86  tff(c_95, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.87/2.86  tff(c_34, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_103, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_34])).
% 7.87/2.86  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_74, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.86  tff(c_92, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_74])).
% 7.87/2.86  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.87/2.86  tff(c_91, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_18, c_74])).
% 7.87/2.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.86  tff(c_325, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.87/2.86  tff(c_349, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_6, c_325])).
% 7.87/2.86  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.87/2.86  tff(c_468, plain, (![A_62, B_63, B_64]: (r1_tarski(A_62, k2_xboole_0(k2_xboole_0(A_62, B_63), B_64)))), inference(resolution, [status(thm)], [c_349, c_12])).
% 7.87/2.86  tff(c_526, plain, (![A_65, B_66, B_67]: (r1_tarski(k4_xboole_0(A_65, B_66), k2_xboole_0(A_65, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_468])).
% 7.87/2.86  tff(c_558, plain, (![B_66]: (r1_tarski(k4_xboole_0('#skF_1', B_66), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_526])).
% 7.87/2.86  tff(c_20, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.87/2.86  tff(c_28, plain, (![C_19, A_17, B_18]: (k6_subset_1(k9_relat_1(C_19, A_17), k9_relat_1(C_19, B_18))=k9_relat_1(C_19, k6_subset_1(A_17, B_18)) | ~v2_funct_1(C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.87/2.86  tff(c_1119, plain, (![C_91, A_92, B_93]: (k4_xboole_0(k9_relat_1(C_91, A_92), k9_relat_1(C_91, B_93))=k9_relat_1(C_91, k4_xboole_0(A_92, B_93)) | ~v2_funct_1(C_91) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_28])).
% 7.87/2.86  tff(c_40, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.86  tff(c_165, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_145])).
% 7.87/2.86  tff(c_1137, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1119, c_165])).
% 7.87/2.86  tff(c_1175, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_1137])).
% 7.87/2.86  tff(c_733, plain, (![A_74, B_75]: (r1_tarski(A_74, k10_relat_1(B_75, k9_relat_1(B_75, A_74))) | ~r1_tarski(A_74, k1_relat_1(B_75)) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.87/2.86  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.86  tff(c_5262, plain, (![A_184, B_185]: (k2_xboole_0(A_184, k10_relat_1(B_185, k9_relat_1(B_185, A_184)))=k10_relat_1(B_185, k9_relat_1(B_185, A_184)) | ~r1_tarski(A_184, k1_relat_1(B_185)) | ~v1_relat_1(B_185))), inference(resolution, [status(thm)], [c_733, c_14])).
% 7.87/2.86  tff(c_5405, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k10_relat_1('#skF_3', k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1175, c_5262])).
% 7.87/2.86  tff(c_5433, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k10_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_558, c_1175, c_5405])).
% 7.87/2.86  tff(c_8821, plain, (![C_244]: (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), C_244) | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), C_244))), inference(superposition, [status(thm), theory('equality')], [c_5433, c_12])).
% 7.87/2.86  tff(c_220, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.86  tff(c_237, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_220])).
% 7.87/2.86  tff(c_8838, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_8821, c_237])).
% 7.87/2.86  tff(c_8853, plain, (~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_103, c_8838])).
% 7.87/2.86  tff(c_8860, plain, (k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_8853])).
% 7.87/2.86  tff(c_13361, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13357, c_8860])).
% 7.87/2.86  tff(c_13372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_13361])).
% 7.87/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.86  
% 7.87/2.86  Inference rules
% 7.87/2.86  ----------------------
% 7.87/2.86  #Ref     : 0
% 7.87/2.86  #Sup     : 3293
% 7.87/2.86  #Fact    : 0
% 7.87/2.86  #Define  : 0
% 7.87/2.86  #Split   : 3
% 7.87/2.86  #Chain   : 0
% 7.87/2.86  #Close   : 0
% 7.87/2.86  
% 7.87/2.86  Ordering : KBO
% 7.87/2.86  
% 7.87/2.86  Simplification rules
% 7.87/2.86  ----------------------
% 7.87/2.86  #Subsume      : 272
% 7.87/2.86  #Demod        : 2947
% 7.87/2.86  #Tautology    : 2234
% 7.87/2.86  #SimpNegUnit  : 5
% 7.87/2.86  #BackRed      : 11
% 7.87/2.86  
% 7.87/2.86  #Partial instantiations: 0
% 7.87/2.86  #Strategies tried      : 1
% 7.87/2.86  
% 7.87/2.86  Timing (in seconds)
% 7.87/2.86  ----------------------
% 7.87/2.86  Preprocessing        : 0.30
% 7.87/2.86  Parsing              : 0.15
% 7.87/2.86  CNF conversion       : 0.02
% 7.87/2.86  Main loop            : 1.80
% 7.87/2.86  Inferencing          : 0.46
% 7.87/2.86  Reduction            : 0.80
% 7.87/2.86  Demodulation         : 0.64
% 7.87/2.86  BG Simplification    : 0.05
% 7.87/2.86  Subsumption          : 0.38
% 7.87/2.86  Abstraction          : 0.08
% 7.87/2.86  MUC search           : 0.00
% 7.87/2.86  Cooper               : 0.00
% 7.87/2.86  Total                : 2.13
% 7.87/2.86  Index Insertion      : 0.00
% 7.87/2.87  Index Deletion       : 0.00
% 7.87/2.87  Index Matching       : 0.00
% 7.87/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
