%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 164 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_261,plain,(
    ! [C_70,A_71,B_72] :
      ( k3_xboole_0(k10_relat_1(C_70,A_71),k10_relat_1(C_70,B_72)) = k10_relat_1(C_70,k3_xboole_0(A_71,B_72))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_24])).

tff(c_278,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_55])).

tff(c_286,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_42,c_278])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_2'(A_9,B_10,C_11),k2_relat_1(C_11))
      | ~ r2_hidden(A_9,k10_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_2'(A_9,B_10,C_11),B_10)
      | ~ r2_hidden(A_9,k10_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,B_30)
      | ~ r2_hidden(C_31,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | k3_xboole_0(A_40,B_39) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_117,plain,(
    ! [A_43,B_44,A_45] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),A_45)
      | k3_xboole_0(A_45,B_44) != k1_xboole_0
      | r1_xboole_0(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_126,plain,(
    ! [B_46,A_47] :
      ( k3_xboole_0(B_46,B_46) != k1_xboole_0
      | r1_xboole_0(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_131,plain,(
    ! [A_48] : r1_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [C_49,A_50] :
      ( ~ r2_hidden(C_49,k1_xboole_0)
      | ~ r2_hidden(C_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_131,c_6])).

tff(c_323,plain,(
    ! [A_82,C_83,A_84] :
      ( ~ r2_hidden('#skF_2'(A_82,k1_xboole_0,C_83),A_84)
      | ~ r2_hidden(A_82,k10_relat_1(C_83,k1_xboole_0))
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_334,plain,(
    ! [A_85,C_86] :
      ( ~ r2_hidden(A_85,k10_relat_1(C_86,k1_xboole_0))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_20,c_323])).

tff(c_371,plain,(
    ! [C_91,A_92] :
      ( ~ v1_relat_1(C_91)
      | r1_xboole_0(A_92,k10_relat_1(C_91,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_334])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_387,plain,(
    ! [A_95,C_96] :
      ( k3_xboole_0(A_95,k10_relat_1(C_96,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k3_xboole_0(k10_relat_1(C_17,A_15),k10_relat_1(C_17,B_16)) = k10_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_394,plain,(
    ! [C_96,A_15] :
      ( k10_relat_1(C_96,k3_xboole_0(A_15,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_22])).

tff(c_471,plain,(
    ! [C_99] :
      ( k10_relat_1(C_99,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_394])).

tff(c_473,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_471])).

tff(c_476,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.31  
% 2.51/1.32  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 2.51/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.51/1.32  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.51/1.32  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.51/1.32  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.51/1.32  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.51/1.32  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.32  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.32  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.32  tff(c_38, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.32  tff(c_42, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.51/1.32  tff(c_261, plain, (![C_70, A_71, B_72]: (k3_xboole_0(k10_relat_1(C_70, A_71), k10_relat_1(C_70, B_72))=k10_relat_1(C_70, k3_xboole_0(A_71, B_72)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.51/1.32  tff(c_47, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.32  tff(c_24, plain, (~r1_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.32  tff(c_55, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_24])).
% 2.51/1.32  tff(c_278, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_55])).
% 2.51/1.32  tff(c_286, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_42, c_278])).
% 2.51/1.32  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.32  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.32  tff(c_20, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_2'(A_9, B_10, C_11), k2_relat_1(C_11)) | ~r2_hidden(A_9, k10_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.32  tff(c_16, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_2'(A_9, B_10, C_11), B_10) | ~r2_hidden(A_9, k10_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.32  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.32  tff(c_58, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, B_30) | ~r2_hidden(C_31, A_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.32  tff(c_106, plain, (![C_38, B_39, A_40]: (~r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | k3_xboole_0(A_40, B_39)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.51/1.32  tff(c_117, plain, (![A_43, B_44, A_45]: (~r2_hidden('#skF_1'(A_43, B_44), A_45) | k3_xboole_0(A_45, B_44)!=k1_xboole_0 | r1_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_8, c_106])).
% 2.51/1.32  tff(c_126, plain, (![B_46, A_47]: (k3_xboole_0(B_46, B_46)!=k1_xboole_0 | r1_xboole_0(A_47, B_46))), inference(resolution, [status(thm)], [c_8, c_117])).
% 2.51/1.32  tff(c_131, plain, (![A_48]: (r1_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_126])).
% 2.51/1.32  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.32  tff(c_140, plain, (![C_49, A_50]: (~r2_hidden(C_49, k1_xboole_0) | ~r2_hidden(C_49, A_50))), inference(resolution, [status(thm)], [c_131, c_6])).
% 2.51/1.32  tff(c_323, plain, (![A_82, C_83, A_84]: (~r2_hidden('#skF_2'(A_82, k1_xboole_0, C_83), A_84) | ~r2_hidden(A_82, k10_relat_1(C_83, k1_xboole_0)) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_16, c_140])).
% 2.51/1.32  tff(c_334, plain, (![A_85, C_86]: (~r2_hidden(A_85, k10_relat_1(C_86, k1_xboole_0)) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_20, c_323])).
% 2.51/1.32  tff(c_371, plain, (![C_91, A_92]: (~v1_relat_1(C_91) | r1_xboole_0(A_92, k10_relat_1(C_91, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_334])).
% 2.51/1.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.32  tff(c_387, plain, (![A_95, C_96]: (k3_xboole_0(A_95, k10_relat_1(C_96, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_371, c_2])).
% 2.51/1.32  tff(c_22, plain, (![C_17, A_15, B_16]: (k3_xboole_0(k10_relat_1(C_17, A_15), k10_relat_1(C_17, B_16))=k10_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.51/1.32  tff(c_394, plain, (![C_96, A_15]: (k10_relat_1(C_96, k3_xboole_0(A_15, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_387, c_22])).
% 2.51/1.32  tff(c_471, plain, (![C_99]: (k10_relat_1(C_99, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_99) | ~v1_relat_1(C_99) | ~v1_relat_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_394])).
% 2.51/1.32  tff(c_473, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_471])).
% 2.51/1.32  tff(c_476, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_473])).
% 2.51/1.32  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_476])).
% 2.51/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  
% 2.51/1.32  Inference rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Ref     : 0
% 2.51/1.32  #Sup     : 105
% 2.51/1.32  #Fact    : 0
% 2.51/1.32  #Define  : 0
% 2.51/1.32  #Split   : 1
% 2.51/1.32  #Chain   : 0
% 2.51/1.32  #Close   : 0
% 2.51/1.32  
% 2.51/1.32  Ordering : KBO
% 2.51/1.32  
% 2.51/1.32  Simplification rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Subsume      : 18
% 2.51/1.32  #Demod        : 24
% 2.51/1.32  #Tautology    : 35
% 2.51/1.32  #SimpNegUnit  : 1
% 2.51/1.32  #BackRed      : 0
% 2.51/1.32  
% 2.51/1.32  #Partial instantiations: 0
% 2.51/1.32  #Strategies tried      : 1
% 2.51/1.32  
% 2.51/1.32  Timing (in seconds)
% 2.51/1.32  ----------------------
% 2.51/1.33  Preprocessing        : 0.28
% 2.51/1.33  Parsing              : 0.16
% 2.51/1.33  CNF conversion       : 0.02
% 2.51/1.33  Main loop            : 0.27
% 2.51/1.33  Inferencing          : 0.11
% 2.51/1.33  Reduction            : 0.07
% 2.51/1.33  Demodulation         : 0.05
% 2.51/1.33  BG Simplification    : 0.01
% 2.51/1.33  Subsumption          : 0.06
% 2.51/1.33  Abstraction          : 0.01
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.58
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
