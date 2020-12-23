%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :   73 (  92 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 167 expanded)
%              Number of equality atoms :   51 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_219,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_227,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_219,c_30])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_78])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1266,plain,(
    ! [C_93,A_94,B_95] :
      ( k4_xboole_0(k9_relat_1(C_93,A_94),k9_relat_1(C_93,B_95)) = k9_relat_1(C_93,k4_xboole_0(A_94,B_95))
      | ~ v2_funct_1(C_93)
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_28])).

tff(c_36,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_91,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_1305,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_91])).

tff(c_1334,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_1305])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_341,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1555,plain,(
    ! [A_105,B_106,A_107] :
      ( r1_tarski(A_105,B_106)
      | ~ r1_tarski(A_105,A_107)
      | k4_xboole_0(A_107,B_106) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_341])).

tff(c_4419,plain,(
    ! [A_163,B_164,B_165] :
      ( r1_tarski(A_163,B_164)
      | k4_xboole_0(B_165,B_164) != k1_xboole_0
      | k4_xboole_0(A_163,B_165) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1555])).

tff(c_4461,plain,(
    ! [A_163] :
      ( r1_tarski(A_163,k1_relat_1('#skF_3'))
      | k4_xboole_0(A_163,'#skF_1') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4419])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_286,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_286])).

tff(c_298,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_295])).

tff(c_849,plain,(
    ! [B_78,A_79] :
      ( r1_xboole_0(k1_relat_1(B_78),A_79)
      | k9_relat_1(B_78,A_79) != k1_xboole_0
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1952,plain,(
    ! [B_119,A_120] :
      ( k3_xboole_0(k1_relat_1(B_119),A_120) = k1_xboole_0
      | k9_relat_1(B_119,A_120) != k1_xboole_0
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_849,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1958,plain,(
    ! [B_119,A_120] :
      ( k5_xboole_0(k1_relat_1(B_119),k1_xboole_0) = k4_xboole_0(k1_relat_1(B_119),A_120)
      | k9_relat_1(B_119,A_120) != k1_xboole_0
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1952,c_10])).

tff(c_5881,plain,(
    ! [B_185,A_186] :
      ( k4_xboole_0(k1_relat_1(B_185),A_186) = k1_relat_1(B_185)
      | k9_relat_1(B_185,A_186) != k1_xboole_0
      | ~ v1_relat_1(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_1958])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19648,plain,(
    ! [A_396,B_397] :
      ( k1_xboole_0 = A_396
      | ~ r1_tarski(A_396,k1_relat_1(B_397))
      | k9_relat_1(B_397,A_396) != k1_xboole_0
      | ~ v1_relat_1(B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5881,c_16])).

tff(c_19709,plain,(
    ! [A_163] :
      ( k1_xboole_0 = A_163
      | k9_relat_1('#skF_3',A_163) != k1_xboole_0
      | ~ v1_relat_1('#skF_3')
      | k4_xboole_0(A_163,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4461,c_19648])).

tff(c_19943,plain,(
    ! [A_399] :
      ( k1_xboole_0 = A_399
      | k9_relat_1('#skF_3',A_399) != k1_xboole_0
      | k4_xboole_0(A_399,'#skF_1') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_19709])).

tff(c_19985,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_19943])).

tff(c_20007,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_19985])).

tff(c_20009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_20007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.63  
% 9.16/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.64  %$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.16/3.64  
% 9.16/3.64  %Foreground sorts:
% 9.16/3.64  
% 9.16/3.64  
% 9.16/3.64  %Background operators:
% 9.16/3.64  
% 9.16/3.64  
% 9.16/3.64  %Foreground operators:
% 9.16/3.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.16/3.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.16/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.16/3.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.16/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.16/3.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.16/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.16/3.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.16/3.64  tff('#skF_2', type, '#skF_2': $i).
% 9.16/3.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.16/3.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.16/3.64  tff('#skF_3', type, '#skF_3': $i).
% 9.16/3.64  tff('#skF_1', type, '#skF_1': $i).
% 9.16/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.16/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.16/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.16/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.16/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.16/3.64  
% 9.16/3.65  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.16/3.65  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 9.16/3.65  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.16/3.65  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.16/3.65  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 9.16/3.65  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.16/3.65  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.16/3.65  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.16/3.65  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.16/3.65  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.16/3.65  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 9.16/3.65  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 9.16/3.65  tff(c_219, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | k4_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.65  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_227, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_219, c_30])).
% 9.16/3.65  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.16/3.65  tff(c_78, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.65  tff(c_93, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_78])).
% 9.16/3.65  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_22, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.16/3.65  tff(c_28, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.16/3.65  tff(c_1266, plain, (![C_93, A_94, B_95]: (k4_xboole_0(k9_relat_1(C_93, A_94), k9_relat_1(C_93, B_95))=k9_relat_1(C_93, k4_xboole_0(A_94, B_95)) | ~v2_funct_1(C_93) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_28])).
% 9.16/3.65  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_91, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_78])).
% 9.16/3.65  tff(c_1305, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_91])).
% 9.16/3.65  tff(c_1334, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_1305])).
% 9.16/3.65  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.65  tff(c_94, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_78])).
% 9.16/3.65  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.65  tff(c_341, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.16/3.65  tff(c_1555, plain, (![A_105, B_106, A_107]: (r1_tarski(A_105, B_106) | ~r1_tarski(A_105, A_107) | k4_xboole_0(A_107, B_106)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_341])).
% 9.16/3.65  tff(c_4419, plain, (![A_163, B_164, B_165]: (r1_tarski(A_163, B_164) | k4_xboole_0(B_165, B_164)!=k1_xboole_0 | k4_xboole_0(A_163, B_165)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1555])).
% 9.16/3.65  tff(c_4461, plain, (![A_163]: (r1_tarski(A_163, k1_relat_1('#skF_3')) | k4_xboole_0(A_163, '#skF_1')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_4419])).
% 9.16/3.65  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.16/3.65  tff(c_20, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.16/3.65  tff(c_66, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.16/3.65  tff(c_70, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_66])).
% 9.16/3.65  tff(c_286, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.16/3.65  tff(c_295, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_286])).
% 9.16/3.65  tff(c_298, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_295])).
% 9.16/3.65  tff(c_849, plain, (![B_78, A_79]: (r1_xboole_0(k1_relat_1(B_78), A_79) | k9_relat_1(B_78, A_79)!=k1_xboole_0 | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.16/3.65  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.16/3.65  tff(c_1952, plain, (![B_119, A_120]: (k3_xboole_0(k1_relat_1(B_119), A_120)=k1_xboole_0 | k9_relat_1(B_119, A_120)!=k1_xboole_0 | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_849, c_2])).
% 9.16/3.65  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.16/3.65  tff(c_1958, plain, (![B_119, A_120]: (k5_xboole_0(k1_relat_1(B_119), k1_xboole_0)=k4_xboole_0(k1_relat_1(B_119), A_120) | k9_relat_1(B_119, A_120)!=k1_xboole_0 | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_1952, c_10])).
% 9.16/3.65  tff(c_5881, plain, (![B_185, A_186]: (k4_xboole_0(k1_relat_1(B_185), A_186)=k1_relat_1(B_185) | k9_relat_1(B_185, A_186)!=k1_xboole_0 | ~v1_relat_1(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_1958])).
% 9.16/3.65  tff(c_16, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.16/3.65  tff(c_19648, plain, (![A_396, B_397]: (k1_xboole_0=A_396 | ~r1_tarski(A_396, k1_relat_1(B_397)) | k9_relat_1(B_397, A_396)!=k1_xboole_0 | ~v1_relat_1(B_397))), inference(superposition, [status(thm), theory('equality')], [c_5881, c_16])).
% 9.16/3.65  tff(c_19709, plain, (![A_163]: (k1_xboole_0=A_163 | k9_relat_1('#skF_3', A_163)!=k1_xboole_0 | ~v1_relat_1('#skF_3') | k4_xboole_0(A_163, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4461, c_19648])).
% 9.16/3.65  tff(c_19943, plain, (![A_399]: (k1_xboole_0=A_399 | k9_relat_1('#skF_3', A_399)!=k1_xboole_0 | k4_xboole_0(A_399, '#skF_1')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_19709])).
% 9.16/3.65  tff(c_19985, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1334, c_19943])).
% 9.16/3.65  tff(c_20007, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_93, c_19985])).
% 9.16/3.65  tff(c_20009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_20007])).
% 9.16/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.65  
% 9.16/3.65  Inference rules
% 9.16/3.65  ----------------------
% 9.16/3.65  #Ref     : 0
% 9.16/3.65  #Sup     : 4852
% 9.16/3.65  #Fact    : 0
% 9.16/3.65  #Define  : 0
% 9.16/3.65  #Split   : 12
% 9.16/3.65  #Chain   : 0
% 9.16/3.65  #Close   : 0
% 9.16/3.65  
% 9.16/3.65  Ordering : KBO
% 9.16/3.65  
% 9.16/3.65  Simplification rules
% 9.16/3.65  ----------------------
% 9.16/3.65  #Subsume      : 2035
% 9.16/3.65  #Demod        : 4105
% 9.16/3.65  #Tautology    : 2058
% 9.16/3.65  #SimpNegUnit  : 72
% 9.16/3.65  #BackRed      : 27
% 9.16/3.65  
% 9.16/3.65  #Partial instantiations: 0
% 9.16/3.65  #Strategies tried      : 1
% 9.16/3.65  
% 9.16/3.65  Timing (in seconds)
% 9.16/3.65  ----------------------
% 9.16/3.65  Preprocessing        : 0.31
% 9.16/3.65  Parsing              : 0.17
% 9.16/3.65  CNF conversion       : 0.02
% 9.16/3.65  Main loop            : 2.58
% 9.16/3.65  Inferencing          : 0.58
% 9.16/3.65  Reduction            : 1.18
% 9.16/3.65  Demodulation         : 0.93
% 9.16/3.65  BG Simplification    : 0.06
% 9.16/3.65  Subsumption          : 0.65
% 9.16/3.65  Abstraction          : 0.10
% 9.16/3.65  MUC search           : 0.00
% 9.16/3.65  Cooper               : 0.00
% 9.16/3.65  Total                : 2.92
% 9.16/3.65  Index Insertion      : 0.00
% 9.16/3.65  Index Deletion       : 0.00
% 9.16/3.65  Index Matching       : 0.00
% 9.16/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
