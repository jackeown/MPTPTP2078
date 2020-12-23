%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 235 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1056,plain,(
    ! [C_74,A_75,B_76] :
      ( k3_xboole_0(k9_relat_1(C_74,A_75),k9_relat_1(C_74,B_76)) = k9_relat_1(C_74,k3_xboole_0(A_75,B_76))
      | ~ v2_funct_1(C_74)
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_86,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_1068,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_99])).

tff(c_1121,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1068])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,k9_relat_1(B_20,A_19)),A_19)
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1137,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_22])).

tff(c_1148,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1137])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_330,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_343,plain,(
    ! [A_43,A_3,B_4] :
      ( r1_tarski(A_43,A_3)
      | ~ r1_tarski(A_43,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_2849,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1148,c_343])).

tff(c_589,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k10_relat_1(B_60,k9_relat_1(B_60,A_59)))
      | ~ r1_tarski(A_59,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3877,plain,(
    ! [B_124,A_125] :
      ( k10_relat_1(B_124,k9_relat_1(B_124,A_125)) = A_125
      | ~ r1_tarski(k10_relat_1(B_124,k9_relat_1(B_124,A_125)),A_125)
      | ~ r1_tarski(A_125,k1_relat_1(B_124))
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_589,c_2])).

tff(c_3884,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2849,c_3877])).

tff(c_3902,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_3884])).

tff(c_14,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(B_32,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [B_32,A_31] : k3_xboole_0(B_32,A_31) = k3_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_16])).

tff(c_357,plain,(
    ! [A_47,A_48,B_49] :
      ( r1_tarski(A_47,A_48)
      | ~ r1_tarski(A_47,k3_xboole_0(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_373,plain,(
    ! [A_47,B_32,A_31] :
      ( r1_tarski(A_47,B_32)
      | ~ r1_tarski(A_47,k3_xboole_0(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_357])).

tff(c_2848,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1148,c_373])).

tff(c_3910,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3902,c_2848])).

tff(c_3915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.80  
% 4.65/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.80  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.65/1.80  
% 4.65/1.80  %Foreground sorts:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Background operators:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Foreground operators:
% 4.65/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.65/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.65/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.65/1.80  
% 4.78/1.81  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 4.78/1.81  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 4.78/1.81  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.78/1.81  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 4.78/1.81  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.78/1.81  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.78/1.81  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.78/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.78/1.81  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.78/1.81  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.78/1.81  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_1056, plain, (![C_74, A_75, B_76]: (k3_xboole_0(k9_relat_1(C_74, A_75), k9_relat_1(C_74, B_76))=k9_relat_1(C_74, k3_xboole_0(A_75, B_76)) | ~v2_funct_1(C_74) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.81  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.81  tff(c_86, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.78/1.81  tff(c_99, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_86])).
% 4.78/1.81  tff(c_1068, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1056, c_99])).
% 4.78/1.81  tff(c_1121, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1068])).
% 4.78/1.81  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, k9_relat_1(B_20, A_19)), A_19) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.78/1.81  tff(c_1137, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1121, c_22])).
% 4.78/1.81  tff(c_1148, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1137])).
% 4.78/1.81  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.78/1.81  tff(c_330, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.81  tff(c_343, plain, (![A_43, A_3, B_4]: (r1_tarski(A_43, A_3) | ~r1_tarski(A_43, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_330])).
% 4.78/1.81  tff(c_2849, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_1148, c_343])).
% 4.78/1.81  tff(c_589, plain, (![A_59, B_60]: (r1_tarski(A_59, k10_relat_1(B_60, k9_relat_1(B_60, A_59))) | ~r1_tarski(A_59, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.78/1.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.78/1.81  tff(c_3877, plain, (![B_124, A_125]: (k10_relat_1(B_124, k9_relat_1(B_124, A_125))=A_125 | ~r1_tarski(k10_relat_1(B_124, k9_relat_1(B_124, A_125)), A_125) | ~r1_tarski(A_125, k1_relat_1(B_124)) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_589, c_2])).
% 4.78/1.81  tff(c_3884, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2849, c_3877])).
% 4.78/1.81  tff(c_3902, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_3884])).
% 4.78/1.81  tff(c_14, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.78/1.81  tff(c_71, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.81  tff(c_124, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(B_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_71])).
% 4.78/1.81  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.81  tff(c_130, plain, (![B_32, A_31]: (k3_xboole_0(B_32, A_31)=k3_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_124, c_16])).
% 4.78/1.81  tff(c_357, plain, (![A_47, A_48, B_49]: (r1_tarski(A_47, A_48) | ~r1_tarski(A_47, k3_xboole_0(A_48, B_49)))), inference(resolution, [status(thm)], [c_8, c_330])).
% 4.78/1.81  tff(c_373, plain, (![A_47, B_32, A_31]: (r1_tarski(A_47, B_32) | ~r1_tarski(A_47, k3_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_357])).
% 4.78/1.81  tff(c_2848, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_2')), inference(resolution, [status(thm)], [c_1148, c_373])).
% 4.78/1.81  tff(c_3910, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3902, c_2848])).
% 4.78/1.81  tff(c_3915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_3910])).
% 4.78/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.81  
% 4.78/1.81  Inference rules
% 4.78/1.81  ----------------------
% 4.78/1.81  #Ref     : 0
% 4.78/1.81  #Sup     : 934
% 4.78/1.81  #Fact    : 0
% 4.78/1.81  #Define  : 0
% 4.78/1.81  #Split   : 3
% 4.78/1.81  #Chain   : 0
% 4.78/1.81  #Close   : 0
% 4.78/1.81  
% 4.78/1.81  Ordering : KBO
% 4.78/1.81  
% 4.78/1.81  Simplification rules
% 4.78/1.81  ----------------------
% 4.78/1.81  #Subsume      : 110
% 4.78/1.81  #Demod        : 778
% 4.78/1.81  #Tautology    : 546
% 4.78/1.81  #SimpNegUnit  : 1
% 4.78/1.81  #BackRed      : 4
% 4.78/1.81  
% 4.78/1.81  #Partial instantiations: 0
% 4.78/1.81  #Strategies tried      : 1
% 4.78/1.81  
% 4.78/1.81  Timing (in seconds)
% 4.78/1.81  ----------------------
% 4.78/1.81  Preprocessing        : 0.29
% 4.78/1.81  Parsing              : 0.16
% 4.78/1.81  CNF conversion       : 0.02
% 4.78/1.81  Main loop            : 0.78
% 4.78/1.81  Inferencing          : 0.22
% 4.78/1.81  Reduction            : 0.34
% 4.78/1.81  Demodulation         : 0.28
% 4.78/1.81  BG Simplification    : 0.03
% 4.78/1.81  Subsumption          : 0.15
% 4.78/1.81  Abstraction          : 0.04
% 4.78/1.81  MUC search           : 0.00
% 4.78/1.81  Cooper               : 0.00
% 4.78/1.81  Total                : 1.10
% 4.78/1.81  Index Insertion      : 0.00
% 4.78/1.81  Index Deletion       : 0.00
% 4.78/1.81  Index Matching       : 0.00
% 4.78/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
