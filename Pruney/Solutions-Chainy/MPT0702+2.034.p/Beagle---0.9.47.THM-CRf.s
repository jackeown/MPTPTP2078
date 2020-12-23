%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 260 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 593 expanded)
%              Number of equality atoms :   37 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_229,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1168,plain,(
    ! [A_81,B_82,A_83] :
      ( r1_tarski(A_81,B_82)
      | ~ r1_tarski(A_81,A_83)
      | k4_xboole_0(A_83,B_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_4459,plain,(
    ! [A_153,B_154,B_155] :
      ( r1_tarski(A_153,B_154)
      | k4_xboole_0(B_155,B_154) != k1_xboole_0
      | k4_xboole_0(A_153,B_155) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1168])).

tff(c_4506,plain,(
    ! [A_153] :
      ( r1_tarski(A_153,k1_relat_1('#skF_3'))
      | k4_xboole_0(A_153,'#skF_1') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4459])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_24])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [B_28] : k4_xboole_0(B_28,B_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_79,plain,(
    ! [B_28] : r1_tarski(k1_xboole_0,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_288,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_229])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_298,plain,(
    ! [A_44] :
      ( k4_xboole_0(A_44,k1_relat_1('#skF_3')) = k1_xboole_0
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_288,c_10])).

tff(c_84,plain,(
    ! [B_29] : r1_tarski(k1_xboole_0,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_88,plain,(
    ! [B_29] : k4_xboole_0(k1_xboole_0,B_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_10])).

tff(c_16,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k9_relat_1(C_14,A_12),k9_relat_1(C_14,B_13)) = k9_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v2_funct_1(C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_952,plain,(
    ! [C_77,A_78,B_79] :
      ( k4_xboole_0(k9_relat_1(C_77,A_78),k9_relat_1(C_77,B_79)) = k9_relat_1(C_77,k4_xboole_0(A_78,B_79))
      | ~ v2_funct_1(C_77)
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_18])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_976,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_69])).

tff(c_999,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_976])).

tff(c_35,plain,(
    ! [C_14,A_12,B_13] :
      ( k4_xboole_0(k9_relat_1(C_14,A_12),k9_relat_1(C_14,B_13)) = k9_relat_1(C_14,k4_xboole_0(A_12,B_13))
      | ~ v2_funct_1(C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_18])).

tff(c_1008,plain,(
    ! [B_13] :
      ( k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_13)) = k4_xboole_0(k1_xboole_0,k9_relat_1('#skF_3',B_13))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_35])).

tff(c_1105,plain,(
    ! [B_80] : k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_80)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_88,c_1008])).

tff(c_1125,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_1105])).

tff(c_1143,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1125])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,k9_relat_1(B_18,A_17)),A_17)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1156,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_22])).

tff(c_1166,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1156])).

tff(c_108,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_28] :
      ( k1_xboole_0 = B_28
      | ~ r1_tarski(B_28,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_79,c_108])).

tff(c_1248,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1166,c_121])).

tff(c_598,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,k10_relat_1(B_58,k9_relat_1(B_58,A_57)))
      | ~ r1_tarski(A_57,k1_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4845,plain,(
    ! [B_158,A_159] :
      ( k10_relat_1(B_158,k9_relat_1(B_158,A_159)) = A_159
      | ~ r1_tarski(k10_relat_1(B_158,k9_relat_1(B_158,A_159)),A_159)
      | ~ r1_tarski(A_159,k1_relat_1(B_158))
      | ~ v1_relat_1(B_158) ) ),
    inference(resolution,[status(thm)],[c_598,c_2])).

tff(c_4874,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_4845])).

tff(c_4909,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_79,c_1248,c_1248,c_999,c_4874])).

tff(c_4910,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4909])).

tff(c_4918,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4506,c_4910])).

tff(c_4940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.91  
% 4.56/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.91  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.56/1.91  
% 4.56/1.91  %Foreground sorts:
% 4.56/1.91  
% 4.56/1.91  
% 4.56/1.91  %Background operators:
% 4.56/1.91  
% 4.56/1.91  
% 4.56/1.91  %Foreground operators:
% 4.56/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.91  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.56/1.91  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.56/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.91  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.56/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.91  
% 4.83/1.93  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.83/1.93  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.83/1.93  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.83/1.93  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.83/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.83/1.93  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.83/1.93  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 4.83/1.93  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.83/1.93  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.83/1.93  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.93  tff(c_53, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.93  tff(c_71, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_53])).
% 4.83/1.93  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_72, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_53])).
% 4.83/1.93  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.93  tff(c_229, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.83/1.93  tff(c_1168, plain, (![A_81, B_82, A_83]: (r1_tarski(A_81, B_82) | ~r1_tarski(A_81, A_83) | k4_xboole_0(A_83, B_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_229])).
% 4.83/1.93  tff(c_4459, plain, (![A_153, B_154, B_155]: (r1_tarski(A_153, B_154) | k4_xboole_0(B_155, B_154)!=k1_xboole_0 | k4_xboole_0(A_153, B_155)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1168])).
% 4.83/1.93  tff(c_4506, plain, (![A_153]: (r1_tarski(A_153, k1_relat_1('#skF_3')) | k4_xboole_0(A_153, '#skF_1')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_4459])).
% 4.83/1.93  tff(c_48, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | k4_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.93  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_52, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_24])).
% 4.83/1.93  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.93  tff(c_74, plain, (![B_28]: (k4_xboole_0(B_28, B_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_53])).
% 4.83/1.93  tff(c_79, plain, (![B_28]: (r1_tarski(k1_xboole_0, B_28))), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 4.83/1.93  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_288, plain, (![A_44]: (r1_tarski(A_44, k1_relat_1('#skF_3')) | ~r1_tarski(A_44, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_229])).
% 4.83/1.93  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.93  tff(c_298, plain, (![A_44]: (k4_xboole_0(A_44, k1_relat_1('#skF_3'))=k1_xboole_0 | ~r1_tarski(A_44, '#skF_1'))), inference(resolution, [status(thm)], [c_288, c_10])).
% 4.83/1.93  tff(c_84, plain, (![B_29]: (r1_tarski(k1_xboole_0, B_29))), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 4.83/1.93  tff(c_88, plain, (![B_29]: (k4_xboole_0(k1_xboole_0, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_10])).
% 4.83/1.93  tff(c_16, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.83/1.93  tff(c_18, plain, (![C_14, A_12, B_13]: (k6_subset_1(k9_relat_1(C_14, A_12), k9_relat_1(C_14, B_13))=k9_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v2_funct_1(C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.83/1.93  tff(c_952, plain, (![C_77, A_78, B_79]: (k4_xboole_0(k9_relat_1(C_77, A_78), k9_relat_1(C_77, B_79))=k9_relat_1(C_77, k4_xboole_0(A_78, B_79)) | ~v2_funct_1(C_77) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_18])).
% 4.83/1.93  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.93  tff(c_69, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_53])).
% 4.83/1.93  tff(c_976, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_952, c_69])).
% 4.83/1.93  tff(c_999, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_976])).
% 4.83/1.93  tff(c_35, plain, (![C_14, A_12, B_13]: (k4_xboole_0(k9_relat_1(C_14, A_12), k9_relat_1(C_14, B_13))=k9_relat_1(C_14, k4_xboole_0(A_12, B_13)) | ~v2_funct_1(C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_18])).
% 4.83/1.93  tff(c_1008, plain, (![B_13]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_13))=k4_xboole_0(k1_xboole_0, k9_relat_1('#skF_3', B_13)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_999, c_35])).
% 4.83/1.93  tff(c_1105, plain, (![B_80]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_80))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_88, c_1008])).
% 4.83/1.93  tff(c_1125, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_298, c_1105])).
% 4.83/1.93  tff(c_1143, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1125])).
% 4.83/1.93  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, k9_relat_1(B_18, A_17)), A_17) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.93  tff(c_1156, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_22])).
% 4.83/1.93  tff(c_1166, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1156])).
% 4.83/1.93  tff(c_108, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.93  tff(c_121, plain, (![B_28]: (k1_xboole_0=B_28 | ~r1_tarski(B_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_79, c_108])).
% 4.83/1.93  tff(c_1248, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1166, c_121])).
% 4.83/1.93  tff(c_598, plain, (![A_57, B_58]: (r1_tarski(A_57, k10_relat_1(B_58, k9_relat_1(B_58, A_57))) | ~r1_tarski(A_57, k1_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/1.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.93  tff(c_4845, plain, (![B_158, A_159]: (k10_relat_1(B_158, k9_relat_1(B_158, A_159))=A_159 | ~r1_tarski(k10_relat_1(B_158, k9_relat_1(B_158, A_159)), A_159) | ~r1_tarski(A_159, k1_relat_1(B_158)) | ~v1_relat_1(B_158))), inference(resolution, [status(thm)], [c_598, c_2])).
% 4.83/1.93  tff(c_4874, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_999, c_4845])).
% 4.83/1.93  tff(c_4909, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_79, c_1248, c_1248, c_999, c_4874])).
% 4.83/1.93  tff(c_4910, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4909])).
% 4.83/1.93  tff(c_4918, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4506, c_4910])).
% 4.83/1.93  tff(c_4940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_4918])).
% 4.83/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.93  
% 4.83/1.93  Inference rules
% 4.83/1.93  ----------------------
% 4.83/1.93  #Ref     : 0
% 4.83/1.93  #Sup     : 1173
% 4.83/1.93  #Fact    : 0
% 4.83/1.93  #Define  : 0
% 4.83/1.93  #Split   : 4
% 4.83/1.93  #Chain   : 0
% 4.83/1.93  #Close   : 0
% 4.83/1.93  
% 4.83/1.93  Ordering : KBO
% 4.83/1.93  
% 4.83/1.93  Simplification rules
% 4.83/1.93  ----------------------
% 4.83/1.93  #Subsume      : 257
% 4.83/1.93  #Demod        : 1036
% 4.83/1.93  #Tautology    : 569
% 4.83/1.93  #SimpNegUnit  : 1
% 4.83/1.93  #BackRed      : 4
% 4.83/1.93  
% 4.83/1.93  #Partial instantiations: 0
% 4.83/1.93  #Strategies tried      : 1
% 4.83/1.93  
% 4.83/1.93  Timing (in seconds)
% 4.83/1.93  ----------------------
% 4.83/1.93  Preprocessing        : 0.31
% 4.83/1.93  Parsing              : 0.17
% 4.83/1.93  CNF conversion       : 0.02
% 4.83/1.93  Main loop            : 0.82
% 4.83/1.93  Inferencing          : 0.25
% 4.83/1.93  Reduction            : 0.31
% 4.83/1.93  Demodulation         : 0.23
% 4.83/1.93  BG Simplification    : 0.03
% 4.83/1.93  Subsumption          : 0.18
% 4.83/1.93  Abstraction          : 0.04
% 4.83/1.93  MUC search           : 0.00
% 4.83/1.93  Cooper               : 0.00
% 4.83/1.93  Total                : 1.16
% 4.83/1.93  Index Insertion      : 0.00
% 4.83/1.93  Index Deletion       : 0.00
% 4.83/1.93  Index Matching       : 0.00
% 4.83/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
