%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 107 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_74,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_75,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | ~ r1_xboole_0(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_75])).

tff(c_16,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_50),k1_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [A_18,B_51] :
      ( k5_relat_1(k6_relat_1(A_18),B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_18,k1_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_172])).

tff(c_347,plain,(
    ! [A_63,B_64] :
      ( k5_relat_1(k6_relat_1(A_63),B_64) = k1_xboole_0
      | ~ r1_xboole_0(A_63,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_181])).

tff(c_356,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_347])).

tff(c_365,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_356])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_371,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_30])).

tff(c_378,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_371])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_378])).

tff(c_382,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_381,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k3_xboole_0(k1_relat_1(B_20),A_19) = k1_relat_1(k7_relat_1(B_20,A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_451,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),k3_xboole_0(A_80,B_81))
      | r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_463,plain,(
    ! [A_82,B_83] :
      ( ~ v1_xboole_0(k3_xboole_0(A_82,B_83))
      | r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_451,c_2])).

tff(c_482,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(B_86,A_87)))
      | r1_xboole_0(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_463])).

tff(c_491,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_482])).

tff(c_496,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_20,c_491])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:08:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.37  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.48/1.37  
% 2.48/1.37  %Foreground sorts:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Background operators:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Foreground operators:
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.48/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.37  
% 2.48/1.38  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.48/1.38  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.48/1.38  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.48/1.38  tff(f_70, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.48/1.38  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.48/1.38  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.48/1.38  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.38  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.48/1.38  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.48/1.38  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.48/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.48/1.38  tff(c_40, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.38  tff(c_74, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.48/1.38  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.38  tff(c_99, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34])).
% 2.48/1.38  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.38  tff(c_75, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | ~r1_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.38  tff(c_78, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_75])).
% 2.48/1.38  tff(c_16, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.38  tff(c_26, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.38  tff(c_172, plain, (![A_50, B_51]: (k5_relat_1(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_50), k1_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.48/1.38  tff(c_181, plain, (![A_18, B_51]: (k5_relat_1(k6_relat_1(A_18), B_51)=k1_xboole_0 | ~r1_xboole_0(A_18, k1_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_172])).
% 2.48/1.38  tff(c_347, plain, (![A_63, B_64]: (k5_relat_1(k6_relat_1(A_63), B_64)=k1_xboole_0 | ~r1_xboole_0(A_63, k1_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_181])).
% 2.48/1.38  tff(c_356, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_347])).
% 2.48/1.38  tff(c_365, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_356])).
% 2.48/1.38  tff(c_30, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.38  tff(c_371, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_365, c_30])).
% 2.48/1.38  tff(c_378, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_371])).
% 2.48/1.38  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_378])).
% 2.48/1.38  tff(c_382, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.48/1.38  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.38  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.38  tff(c_381, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.48/1.38  tff(c_28, plain, (![B_20, A_19]: (k3_xboole_0(k1_relat_1(B_20), A_19)=k1_relat_1(k7_relat_1(B_20, A_19)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.38  tff(c_451, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), k3_xboole_0(A_80, B_81)) | r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.48/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.38  tff(c_463, plain, (![A_82, B_83]: (~v1_xboole_0(k3_xboole_0(A_82, B_83)) | r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_451, c_2])).
% 2.48/1.38  tff(c_482, plain, (![B_86, A_87]: (~v1_xboole_0(k1_relat_1(k7_relat_1(B_86, A_87))) | r1_xboole_0(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_28, c_463])).
% 2.48/1.38  tff(c_491, plain, (~v1_xboole_0(k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_381, c_482])).
% 2.48/1.38  tff(c_496, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_20, c_491])).
% 2.48/1.38  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_496])).
% 2.48/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  Inference rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Ref     : 0
% 2.48/1.38  #Sup     : 107
% 2.48/1.38  #Fact    : 0
% 2.48/1.38  #Define  : 0
% 2.48/1.38  #Split   : 3
% 2.48/1.38  #Chain   : 0
% 2.48/1.38  #Close   : 0
% 2.48/1.38  
% 2.48/1.38  Ordering : KBO
% 2.48/1.38  
% 2.48/1.38  Simplification rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Subsume      : 13
% 2.48/1.38  #Demod        : 57
% 2.48/1.38  #Tautology    : 57
% 2.48/1.38  #SimpNegUnit  : 3
% 2.48/1.38  #BackRed      : 0
% 2.48/1.38  
% 2.48/1.38  #Partial instantiations: 0
% 2.48/1.38  #Strategies tried      : 1
% 2.48/1.38  
% 2.48/1.38  Timing (in seconds)
% 2.48/1.38  ----------------------
% 2.48/1.39  Preprocessing        : 0.32
% 2.48/1.39  Parsing              : 0.17
% 2.48/1.39  CNF conversion       : 0.02
% 2.48/1.39  Main loop            : 0.26
% 2.48/1.39  Inferencing          : 0.10
% 2.48/1.39  Reduction            : 0.08
% 2.48/1.39  Demodulation         : 0.06
% 2.48/1.39  BG Simplification    : 0.01
% 2.48/1.39  Subsumption          : 0.04
% 2.48/1.39  Abstraction          : 0.02
% 2.48/1.39  MUC search           : 0.00
% 2.48/1.39  Cooper               : 0.00
% 2.48/1.39  Total                : 0.60
% 2.48/1.39  Index Insertion      : 0.00
% 2.48/1.39  Index Deletion       : 0.00
% 2.48/1.39  Index Matching       : 0.00
% 2.48/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
