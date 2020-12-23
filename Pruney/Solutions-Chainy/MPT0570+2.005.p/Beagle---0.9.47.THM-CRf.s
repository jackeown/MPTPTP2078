%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:42 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  93 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_446,plain,(
    ! [B_83,A_84] :
      ( r1_xboole_0(k2_relat_1(B_83),A_84)
      | k10_relat_1(B_83,A_84) != k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_718,plain,(
    ! [B_99,A_100] :
      ( k4_xboole_0(k2_relat_1(B_99),A_100) = k2_relat_1(B_99)
      | k10_relat_1(B_99,A_100) != k1_xboole_0
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_446,c_12])).

tff(c_96,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [B_62,A_63] : k1_setfam_1(k2_tarski(B_62,A_63)) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_81])).

tff(c_30,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_155,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_30])).

tff(c_241,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_300,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(B_73,A_72)) = k4_xboole_0(A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_241])).

tff(c_329,plain,(
    k5_xboole_0(k2_relat_1('#skF_2'),'#skF_1') = k4_xboole_0(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_300])).

tff(c_172,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_30])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [B_66,A_67] : r1_xboole_0(k3_xboole_0(B_66,A_67),k5_xboole_0(A_67,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_6])).

tff(c_228,plain,(
    r1_xboole_0('#skF_1',k5_xboole_0(k2_relat_1('#skF_2'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_216])).

tff(c_235,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0(k2_relat_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_228,c_12])).

tff(c_338,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0(k2_relat_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_235])).

tff(c_736,plain,
    ( k4_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_338])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_135,c_736])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.37  
% 2.53/1.37  %Foreground sorts:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Background operators:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Foreground operators:
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.53/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.37  
% 2.82/1.38  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.82/1.38  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.82/1.38  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.82/1.38  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.82/1.38  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.82/1.38  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.82/1.38  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.82/1.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.82/1.38  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.82/1.38  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.38  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.38  tff(c_36, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.38  tff(c_38, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.38  tff(c_131, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.38  tff(c_135, plain, (k4_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.82/1.38  tff(c_446, plain, (![B_83, A_84]: (r1_xboole_0(k2_relat_1(B_83), A_84) | k10_relat_1(B_83, A_84)!=k1_xboole_0 | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.82/1.38  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.38  tff(c_718, plain, (![B_99, A_100]: (k4_xboole_0(k2_relat_1(B_99), A_100)=k2_relat_1(B_99) | k10_relat_1(B_99, A_100)!=k1_xboole_0 | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_446, c_12])).
% 2.82/1.38  tff(c_96, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.38  tff(c_100, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.82/1.38  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.38  tff(c_81, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.38  tff(c_149, plain, (![B_62, A_63]: (k1_setfam_1(k2_tarski(B_62, A_63))=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_16, c_81])).
% 2.82/1.38  tff(c_30, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.38  tff(c_155, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_149, c_30])).
% 2.82/1.38  tff(c_241, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.38  tff(c_300, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(B_73, A_72))=k4_xboole_0(A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_155, c_241])).
% 2.82/1.38  tff(c_329, plain, (k5_xboole_0(k2_relat_1('#skF_2'), '#skF_1')=k4_xboole_0(k2_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_300])).
% 2.82/1.38  tff(c_172, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_149, c_30])).
% 2.82/1.38  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.38  tff(c_216, plain, (![B_66, A_67]: (r1_xboole_0(k3_xboole_0(B_66, A_67), k5_xboole_0(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_6])).
% 2.82/1.38  tff(c_228, plain, (r1_xboole_0('#skF_1', k5_xboole_0(k2_relat_1('#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_216])).
% 2.82/1.38  tff(c_235, plain, (k4_xboole_0('#skF_1', k5_xboole_0(k2_relat_1('#skF_2'), '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_228, c_12])).
% 2.82/1.38  tff(c_338, plain, (k4_xboole_0('#skF_1', k4_xboole_0(k2_relat_1('#skF_2'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_329, c_235])).
% 2.82/1.38  tff(c_736, plain, (k4_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_718, c_338])).
% 2.82/1.38  tff(c_751, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_135, c_736])).
% 2.82/1.38  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_751])).
% 2.82/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  Inference rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Ref     : 0
% 2.82/1.38  #Sup     : 187
% 2.82/1.38  #Fact    : 0
% 2.82/1.38  #Define  : 0
% 2.82/1.38  #Split   : 0
% 2.82/1.38  #Chain   : 0
% 2.82/1.38  #Close   : 0
% 2.82/1.38  
% 2.82/1.38  Ordering : KBO
% 2.82/1.38  
% 2.82/1.38  Simplification rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Subsume      : 18
% 2.82/1.38  #Demod        : 102
% 2.82/1.38  #Tautology    : 107
% 2.82/1.38  #SimpNegUnit  : 1
% 2.82/1.38  #BackRed      : 2
% 2.82/1.38  
% 2.82/1.38  #Partial instantiations: 0
% 2.82/1.38  #Strategies tried      : 1
% 2.82/1.38  
% 2.82/1.38  Timing (in seconds)
% 2.82/1.38  ----------------------
% 2.82/1.39  Preprocessing        : 0.31
% 2.82/1.39  Parsing              : 0.17
% 2.82/1.39  CNF conversion       : 0.02
% 2.82/1.39  Main loop            : 0.32
% 2.82/1.39  Inferencing          : 0.11
% 2.82/1.39  Reduction            : 0.13
% 2.82/1.39  Demodulation         : 0.10
% 2.82/1.39  BG Simplification    : 0.02
% 2.82/1.39  Subsumption          : 0.04
% 2.82/1.39  Abstraction          : 0.02
% 2.82/1.39  MUC search           : 0.00
% 2.82/1.39  Cooper               : 0.00
% 2.82/1.39  Total                : 0.66
% 2.82/1.39  Index Insertion      : 0.00
% 2.82/1.39  Index Deletion       : 0.00
% 2.82/1.39  Index Matching       : 0.00
% 2.82/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
