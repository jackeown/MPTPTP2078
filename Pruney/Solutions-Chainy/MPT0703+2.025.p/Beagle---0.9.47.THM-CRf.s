%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 142 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_39,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_26])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_94,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_169,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_169])).

tff(c_187,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_178])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_420,plain,(
    ! [B_62,A_63] :
      ( k9_relat_1(B_62,k10_relat_1(B_62,A_63)) = A_63
      | ~ r1_tarski(A_63,k2_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_433,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_420])).

tff(c_445,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_433])).

tff(c_744,plain,(
    ! [C_75,A_76,B_77] :
      ( k3_xboole_0(k10_relat_1(C_75,A_76),k10_relat_1(C_75,B_77)) = k10_relat_1(C_75,k3_xboole_0(A_76,B_77))
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_756,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_114])).

tff(c_791,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_756])).

tff(c_221,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_238,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_45,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_425,plain,(
    ! [A_45] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_45)) = A_45
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_45,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_238,c_420])).

tff(c_892,plain,(
    ! [A_82] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_82)) = A_82
      | ~ r1_tarski(A_82,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_425])).

tff(c_904,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_892])).

tff(c_914,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_445,c_904])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_937,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_12])).

tff(c_951,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_937])).

tff(c_953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_951])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.44  
% 2.62/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.44  
% 2.62/1.44  %Foreground sorts:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Background operators:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Foreground operators:
% 2.62/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.62/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.44  
% 2.62/1.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.62/1.45  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 2.62/1.45  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.62/1.45  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.62/1.45  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.62/1.45  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.62/1.45  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.62/1.45  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.62/1.45  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.62/1.45  tff(c_39, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.45  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.45  tff(c_43, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_26])).
% 2.62/1.45  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.45  tff(c_44, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.45  tff(c_66, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_44])).
% 2.62/1.45  tff(c_94, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.45  tff(c_116, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(resolution, [status(thm)], [c_20, c_94])).
% 2.62/1.45  tff(c_169, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.45  tff(c_178, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k5_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_116, c_169])).
% 2.62/1.45  tff(c_187, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_178])).
% 2.62/1.45  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.45  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.45  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.45  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.45  tff(c_420, plain, (![B_62, A_63]: (k9_relat_1(B_62, k10_relat_1(B_62, A_63))=A_63 | ~r1_tarski(A_63, k2_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.45  tff(c_433, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_420])).
% 2.62/1.45  tff(c_445, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_433])).
% 2.62/1.45  tff(c_744, plain, (![C_75, A_76, B_77]: (k3_xboole_0(k10_relat_1(C_75, A_76), k10_relat_1(C_75, B_77))=k10_relat_1(C_75, k3_xboole_0(A_76, B_77)) | ~v1_funct_1(C_75) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.45  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.45  tff(c_114, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.62/1.45  tff(c_756, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_744, c_114])).
% 2.62/1.45  tff(c_791, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_756])).
% 2.62/1.45  tff(c_221, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.45  tff(c_238, plain, (![A_45]: (r1_tarski(A_45, k2_relat_1('#skF_3')) | ~r1_tarski(A_45, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_221])).
% 2.62/1.45  tff(c_425, plain, (![A_45]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_45))=A_45 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_45, '#skF_1'))), inference(resolution, [status(thm)], [c_238, c_420])).
% 2.62/1.45  tff(c_892, plain, (![A_82]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_82))=A_82 | ~r1_tarski(A_82, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_425])).
% 2.62/1.45  tff(c_904, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_791, c_892])).
% 2.62/1.45  tff(c_914, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_445, c_904])).
% 2.62/1.45  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.45  tff(c_937, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_914, c_12])).
% 2.62/1.45  tff(c_951, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_187, c_937])).
% 2.62/1.45  tff(c_953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_951])).
% 2.62/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.45  
% 2.62/1.45  Inference rules
% 2.62/1.45  ----------------------
% 2.62/1.45  #Ref     : 0
% 2.62/1.45  #Sup     : 221
% 2.62/1.45  #Fact    : 0
% 2.62/1.45  #Define  : 0
% 2.62/1.45  #Split   : 1
% 2.62/1.45  #Chain   : 0
% 2.62/1.45  #Close   : 0
% 2.62/1.45  
% 2.62/1.45  Ordering : KBO
% 2.62/1.45  
% 2.62/1.45  Simplification rules
% 2.62/1.45  ----------------------
% 2.62/1.45  #Subsume      : 9
% 2.62/1.45  #Demod        : 107
% 2.62/1.45  #Tautology    : 133
% 2.62/1.45  #SimpNegUnit  : 1
% 2.62/1.45  #BackRed      : 0
% 2.62/1.45  
% 2.62/1.45  #Partial instantiations: 0
% 2.62/1.45  #Strategies tried      : 1
% 2.62/1.45  
% 2.62/1.45  Timing (in seconds)
% 2.62/1.45  ----------------------
% 2.62/1.45  Preprocessing        : 0.29
% 2.62/1.45  Parsing              : 0.17
% 2.62/1.45  CNF conversion       : 0.02
% 2.62/1.45  Main loop            : 0.34
% 2.62/1.45  Inferencing          : 0.12
% 2.62/1.45  Reduction            : 0.11
% 2.62/1.45  Demodulation         : 0.08
% 2.62/1.46  BG Simplification    : 0.02
% 2.62/1.46  Subsumption          : 0.07
% 2.62/1.46  Abstraction          : 0.02
% 2.62/1.46  MUC search           : 0.00
% 2.62/1.46  Cooper               : 0.00
% 2.62/1.46  Total                : 0.66
% 2.62/1.46  Index Insertion      : 0.00
% 2.62/1.46  Index Deletion       : 0.00
% 2.62/1.46  Index Matching       : 0.00
% 2.62/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
