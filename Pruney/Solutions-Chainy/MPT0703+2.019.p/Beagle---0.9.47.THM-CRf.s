%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 222 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_183,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183,c_24])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [B_26] : r1_tarski(k1_xboole_0,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_256,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_275,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_81,c_256])).

tff(c_278,plain,(
    ! [A_3,B_40] :
      ( r1_tarski(A_3,B_40)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_318,plain,(
    ! [B_40] : r1_tarski(k1_xboole_0,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_278])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( k6_subset_1(k10_relat_1(C_15,A_13),k10_relat_1(C_15,B_14)) = k10_relat_1(C_15,k6_subset_1(A_13,B_14))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_539,plain,(
    ! [C_54,A_55,B_56] :
      ( k4_xboole_0(k10_relat_1(C_54,A_55),k10_relat_1(C_54,B_56)) = k10_relat_1(C_54,k4_xboole_0(A_55,B_56))
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_20])).

tff(c_577,plain,(
    ! [C_54,A_55] :
      ( k10_relat_1(C_54,k4_xboole_0(A_55,A_55)) = k1_xboole_0
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_539])).

tff(c_832,plain,(
    ! [C_65] :
      ( k10_relat_1(C_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_577])).

tff(c_835,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_832])).

tff(c_838,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_835])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_352,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_45,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_256])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(B_17,k10_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k2_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_354,plain,(
    ! [A_45] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_45)) = A_45
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_45,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_352,c_22])).

tff(c_1697,plain,(
    ! [A_94] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_94)) = A_94
      | ~ r1_tarski(A_94,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_354])).

tff(c_1712,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1697])).

tff(c_1727,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_1712])).

tff(c_28,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_10])).

tff(c_551,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_75])).

tff(c_580,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_551])).

tff(c_1715,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_1697])).

tff(c_1729,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1715])).

tff(c_1737,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_1729])).

tff(c_1738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_1737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:04:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.11/1.46  
% 3.11/1.46  %Foreground sorts:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Background operators:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Foreground operators:
% 3.11/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.11/1.46  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.11/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.11/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.46  
% 3.26/1.47  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.26/1.47  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 3.26/1.47  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.26/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.47  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.26/1.47  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.26/1.47  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.26/1.47  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 3.26/1.47  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 3.26/1.47  tff(c_183, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.47  tff(c_191, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_183, c_24])).
% 3.26/1.47  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.47  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.47  tff(c_59, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_76, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.26/1.47  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.47  tff(c_81, plain, (![B_26]: (r1_tarski(k1_xboole_0, B_26))), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 3.26/1.47  tff(c_256, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.47  tff(c_275, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_81, c_256])).
% 3.26/1.47  tff(c_278, plain, (![A_3, B_40]: (r1_tarski(A_3, B_40) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_275])).
% 3.26/1.47  tff(c_318, plain, (![B_40]: (r1_tarski(k1_xboole_0, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_278])).
% 3.26/1.47  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.47  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.47  tff(c_71, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.26/1.47  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.47  tff(c_20, plain, (![C_15, A_13, B_14]: (k6_subset_1(k10_relat_1(C_15, A_13), k10_relat_1(C_15, B_14))=k10_relat_1(C_15, k6_subset_1(A_13, B_14)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.47  tff(c_539, plain, (![C_54, A_55, B_56]: (k4_xboole_0(k10_relat_1(C_54, A_55), k10_relat_1(C_54, B_56))=k10_relat_1(C_54, k4_xboole_0(A_55, B_56)) | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_20])).
% 3.26/1.47  tff(c_577, plain, (![C_54, A_55]: (k10_relat_1(C_54, k4_xboole_0(A_55, A_55))=k1_xboole_0 | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_71, c_539])).
% 3.26/1.47  tff(c_832, plain, (![C_65]: (k10_relat_1(C_65, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_577])).
% 3.26/1.47  tff(c_835, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_832])).
% 3.26/1.47  tff(c_838, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_835])).
% 3.26/1.47  tff(c_26, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.47  tff(c_352, plain, (![A_45]: (r1_tarski(A_45, k2_relat_1('#skF_3')) | ~r1_tarski(A_45, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_256])).
% 3.26/1.47  tff(c_22, plain, (![B_17, A_16]: (k9_relat_1(B_17, k10_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k2_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.47  tff(c_354, plain, (![A_45]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_45))=A_45 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_45, '#skF_1'))), inference(resolution, [status(thm)], [c_352, c_22])).
% 3.26/1.47  tff(c_1697, plain, (![A_94]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_94))=A_94 | ~r1_tarski(A_94, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_354])).
% 3.26/1.47  tff(c_1712, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_838, c_1697])).
% 3.26/1.47  tff(c_1727, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_318, c_1712])).
% 3.26/1.47  tff(c_28, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.47  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_75, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_10])).
% 3.26/1.47  tff(c_551, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_539, c_75])).
% 3.26/1.47  tff(c_580, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_551])).
% 3.26/1.47  tff(c_1715, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_580, c_1697])).
% 3.26/1.47  tff(c_1729, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1715])).
% 3.26/1.47  tff(c_1737, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1727, c_1729])).
% 3.26/1.47  tff(c_1738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_1737])).
% 3.26/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  Inference rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Ref     : 2
% 3.26/1.47  #Sup     : 419
% 3.26/1.47  #Fact    : 0
% 3.26/1.47  #Define  : 0
% 3.26/1.47  #Split   : 2
% 3.26/1.47  #Chain   : 0
% 3.26/1.47  #Close   : 0
% 3.26/1.47  
% 3.26/1.47  Ordering : KBO
% 3.26/1.47  
% 3.26/1.47  Simplification rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Subsume      : 103
% 3.26/1.47  #Demod        : 200
% 3.26/1.47  #Tautology    : 218
% 3.26/1.47  #SimpNegUnit  : 5
% 3.26/1.47  #BackRed      : 0
% 3.26/1.47  
% 3.26/1.47  #Partial instantiations: 0
% 3.26/1.47  #Strategies tried      : 1
% 3.26/1.47  
% 3.26/1.47  Timing (in seconds)
% 3.26/1.47  ----------------------
% 3.26/1.48  Preprocessing        : 0.29
% 3.26/1.48  Parsing              : 0.16
% 3.26/1.48  CNF conversion       : 0.02
% 3.26/1.48  Main loop            : 0.43
% 3.26/1.48  Inferencing          : 0.14
% 3.26/1.48  Reduction            : 0.15
% 3.26/1.48  Demodulation         : 0.11
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.09
% 3.26/1.48  Abstraction          : 0.03
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.75
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
