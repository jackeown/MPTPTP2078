%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 214 expanded)
%              Number of equality atoms :   30 (  54 expanded)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_178,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_186,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_178,c_20])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_226,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(A_36,A_37)
      | ~ r1_tarski(A_36,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_229,plain,(
    ! [A_1,A_37] :
      ( r1_tarski(A_1,A_37)
      | k4_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_226])).

tff(c_247,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_229])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_54])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k10_relat_1(C_14,A_12),k10_relat_1(C_14,B_13)) = k10_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_748,plain,(
    ! [C_61,A_62,B_63] :
      ( k4_xboole_0(k10_relat_1(C_61,A_62),k10_relat_1(C_61,B_63)) = k10_relat_1(C_61,k4_xboole_0(A_62,B_63))
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_792,plain,(
    ! [C_61,A_62] :
      ( k10_relat_1(C_61,k4_xboole_0(A_62,A_62)) = k1_xboole_0
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_748])).

tff(c_819,plain,(
    ! [C_64] :
      ( k10_relat_1(C_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_792])).

tff(c_822,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_819])).

tff(c_825,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_822])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_216,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_32,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_199])).

tff(c_367,plain,(
    ! [B_45,A_46] :
      ( k9_relat_1(B_45,k10_relat_1(B_45,A_46)) = A_46
      | ~ r1_tarski(A_46,k2_relat_1(B_45))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_372,plain,(
    ! [A_32] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_32)) = A_32
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_32,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_216,c_367])).

tff(c_1240,plain,(
    ! [A_80] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_80)) = A_80
      | ~ r1_tarski(A_80,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_372])).

tff(c_1255,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_1240])).

tff(c_1270,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_1255])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_769,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_70])).

tff(c_795,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_769])).

tff(c_1258,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_1240])).

tff(c_1272,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1258])).

tff(c_1280,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1272])).

tff(c_1281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_1280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n017.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:52:46 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.46  
% 2.97/1.46  %Foreground sorts:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Background operators:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Foreground operators:
% 2.97/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.97/1.46  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.97/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.97/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.46  
% 2.97/1.48  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.97/1.48  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 2.97/1.48  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.97/1.48  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.97/1.48  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.97/1.48  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.97/1.48  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.97/1.48  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 2.97/1.48  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.97/1.48  tff(c_178, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.48  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.48  tff(c_186, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_178, c_20])).
% 2.97/1.48  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.97/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.48  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.48  tff(c_199, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.48  tff(c_226, plain, (![A_36, A_37]: (r1_tarski(A_36, A_37) | ~r1_tarski(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_199])).
% 2.97/1.48  tff(c_229, plain, (![A_1, A_37]: (r1_tarski(A_1, A_37) | k4_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_226])).
% 2.97/1.48  tff(c_247, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_229])).
% 2.97/1.48  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.48  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.48  tff(c_40, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.48  tff(c_43, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_40])).
% 2.97/1.48  tff(c_54, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.48  tff(c_71, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_43, c_54])).
% 2.97/1.48  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.97/1.48  tff(c_16, plain, (![C_14, A_12, B_13]: (k6_subset_1(k10_relat_1(C_14, A_12), k10_relat_1(C_14, B_13))=k10_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.48  tff(c_748, plain, (![C_61, A_62, B_63]: (k4_xboole_0(k10_relat_1(C_61, A_62), k10_relat_1(C_61, B_63))=k10_relat_1(C_61, k4_xboole_0(A_62, B_63)) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 2.97/1.48  tff(c_792, plain, (![C_61, A_62]: (k10_relat_1(C_61, k4_xboole_0(A_62, A_62))=k1_xboole_0 | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(superposition, [status(thm), theory('equality')], [c_71, c_748])).
% 2.97/1.48  tff(c_819, plain, (![C_64]: (k10_relat_1(C_64, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_792])).
% 2.97/1.48  tff(c_822, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_819])).
% 2.97/1.48  tff(c_825, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_822])).
% 2.97/1.48  tff(c_22, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.48  tff(c_216, plain, (![A_32]: (r1_tarski(A_32, k2_relat_1('#skF_3')) | ~r1_tarski(A_32, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_199])).
% 2.97/1.48  tff(c_367, plain, (![B_45, A_46]: (k9_relat_1(B_45, k10_relat_1(B_45, A_46))=A_46 | ~r1_tarski(A_46, k2_relat_1(B_45)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.48  tff(c_372, plain, (![A_32]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_32))=A_32 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_32, '#skF_1'))), inference(resolution, [status(thm)], [c_216, c_367])).
% 2.97/1.48  tff(c_1240, plain, (![A_80]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_80))=A_80 | ~r1_tarski(A_80, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_372])).
% 2.97/1.48  tff(c_1255, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_825, c_1240])).
% 2.97/1.48  tff(c_1270, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_247, c_1255])).
% 2.97/1.48  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.48  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.48  tff(c_70, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_54])).
% 2.97/1.48  tff(c_769, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_748, c_70])).
% 2.97/1.48  tff(c_795, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_769])).
% 2.97/1.48  tff(c_1258, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_795, c_1240])).
% 2.97/1.48  tff(c_1272, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1258])).
% 2.97/1.48  tff(c_1280, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1272])).
% 2.97/1.48  tff(c_1281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_1280])).
% 2.97/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  Inference rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Ref     : 0
% 2.97/1.48  #Sup     : 305
% 2.97/1.48  #Fact    : 0
% 2.97/1.48  #Define  : 0
% 2.97/1.48  #Split   : 2
% 2.97/1.48  #Chain   : 0
% 2.97/1.48  #Close   : 0
% 2.97/1.48  
% 2.97/1.48  Ordering : KBO
% 2.97/1.48  
% 2.97/1.48  Simplification rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Subsume      : 48
% 2.97/1.48  #Demod        : 177
% 2.97/1.48  #Tautology    : 176
% 2.97/1.48  #SimpNegUnit  : 1
% 2.97/1.48  #BackRed      : 0
% 2.97/1.48  
% 2.97/1.48  #Partial instantiations: 0
% 2.97/1.48  #Strategies tried      : 1
% 2.97/1.48  
% 2.97/1.48  Timing (in seconds)
% 2.97/1.48  ----------------------
% 2.97/1.48  Preprocessing        : 0.30
% 2.97/1.48  Parsing              : 0.17
% 2.97/1.48  CNF conversion       : 0.02
% 2.97/1.48  Main loop            : 0.39
% 2.97/1.48  Inferencing          : 0.14
% 2.97/1.48  Reduction            : 0.13
% 2.97/1.48  Demodulation         : 0.10
% 2.97/1.48  BG Simplification    : 0.02
% 2.97/1.48  Subsumption          : 0.08
% 2.97/1.48  Abstraction          : 0.02
% 2.97/1.48  MUC search           : 0.00
% 2.97/1.48  Cooper               : 0.00
% 2.97/1.48  Total                : 0.72
% 2.97/1.48  Index Insertion      : 0.00
% 2.97/1.48  Index Deletion       : 0.00
% 2.97/1.48  Index Matching       : 0.00
% 2.97/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
