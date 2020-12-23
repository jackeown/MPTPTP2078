%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 121 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_32,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_112,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_14,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_247,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_48),k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_262,plain,(
    ! [A_14,B_49] :
      ( k5_relat_1(k6_relat_1(A_14),B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_14,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_247])).

tff(c_369,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,k1_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_262])).

tff(c_379,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_369])).

tff(c_397,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_379])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_407,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_28])).

tff(c_414,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_407])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_414])).

tff(c_417,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_426,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(A_61,B_62)
      | k4_xboole_0(A_61,B_62) != A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_437,plain,(
    ! [B_62,A_61] :
      ( r1_xboole_0(B_62,A_61)
      | k4_xboole_0(A_61,B_62) != A_61 ) ),
    inference(resolution,[status(thm)],[c_426,c_2])).

tff(c_450,plain,(
    ! [A_65,B_66] :
      ( ~ r1_xboole_0(k3_xboole_0(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_530,plain,(
    ! [A_76,A_77] :
      ( r1_xboole_0(A_76,A_77)
      | k4_xboole_0(A_77,k3_xboole_0(A_76,A_77)) != A_77 ) ),
    inference(resolution,[status(thm)],[c_437,c_450])).

tff(c_539,plain,(
    ! [A_78] : r1_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_530])).

tff(c_553,plain,(
    ! [A_78] : r1_xboole_0(k1_xboole_0,A_78) ),
    inference(resolution,[status(thm)],[c_539,c_2])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_418,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_497,plain,(
    ! [B_72,A_73] :
      ( k3_xboole_0(k1_relat_1(B_72),A_73) = k1_relat_1(k7_relat_1(B_72,A_73))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( ~ r1_xboole_0(k3_xboole_0(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_630,plain,(
    ! [B_86,A_87] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(B_86,A_87)),A_87)
      | r1_xboole_0(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_6])).

tff(c_648,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),'#skF_1')
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_630])).

tff(c_656,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_553,c_18,c_648])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.38  
% 2.25/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.39  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.39  
% 2.25/1.39  %Foreground sorts:
% 2.25/1.39  
% 2.25/1.39  
% 2.25/1.39  %Background operators:
% 2.25/1.39  
% 2.25/1.39  
% 2.25/1.39  %Foreground operators:
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.39  
% 2.59/1.40  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.59/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.59/1.40  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.59/1.40  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.59/1.40  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.59/1.40  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.59/1.40  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.59/1.40  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.59/1.40  tff(f_37, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.59/1.40  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.59/1.40  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.59/1.40  tff(c_32, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.40  tff(c_83, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.59/1.40  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.40  tff(c_38, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.40  tff(c_112, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_83, c_38])).
% 2.59/1.40  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.40  tff(c_119, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.59/1.40  tff(c_14, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.40  tff(c_24, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.40  tff(c_247, plain, (![A_48, B_49]: (k5_relat_1(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_48), k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.59/1.40  tff(c_262, plain, (![A_14, B_49]: (k5_relat_1(k6_relat_1(A_14), B_49)=k1_xboole_0 | ~r1_xboole_0(A_14, k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_247])).
% 2.59/1.40  tff(c_369, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, k1_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_262])).
% 2.59/1.40  tff(c_379, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_119, c_369])).
% 2.59/1.40  tff(c_397, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_379])).
% 2.59/1.40  tff(c_28, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.40  tff(c_407, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_397, c_28])).
% 2.59/1.40  tff(c_414, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_407])).
% 2.59/1.40  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_414])).
% 2.59/1.40  tff(c_417, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.59/1.40  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.40  tff(c_426, plain, (![A_61, B_62]: (r1_xboole_0(A_61, B_62) | k4_xboole_0(A_61, B_62)!=A_61)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.40  tff(c_437, plain, (![B_62, A_61]: (r1_xboole_0(B_62, A_61) | k4_xboole_0(A_61, B_62)!=A_61)), inference(resolution, [status(thm)], [c_426, c_2])).
% 2.59/1.40  tff(c_450, plain, (![A_65, B_66]: (~r1_xboole_0(k3_xboole_0(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.40  tff(c_530, plain, (![A_76, A_77]: (r1_xboole_0(A_76, A_77) | k4_xboole_0(A_77, k3_xboole_0(A_76, A_77))!=A_77)), inference(resolution, [status(thm)], [c_437, c_450])).
% 2.59/1.40  tff(c_539, plain, (![A_78]: (r1_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_530])).
% 2.59/1.40  tff(c_553, plain, (![A_78]: (r1_xboole_0(k1_xboole_0, A_78))), inference(resolution, [status(thm)], [c_539, c_2])).
% 2.59/1.40  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.40  tff(c_418, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.59/1.40  tff(c_497, plain, (![B_72, A_73]: (k3_xboole_0(k1_relat_1(B_72), A_73)=k1_relat_1(k7_relat_1(B_72, A_73)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.59/1.40  tff(c_6, plain, (![A_4, B_5]: (~r1_xboole_0(k3_xboole_0(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.40  tff(c_630, plain, (![B_86, A_87]: (~r1_xboole_0(k1_relat_1(k7_relat_1(B_86, A_87)), A_87) | r1_xboole_0(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_497, c_6])).
% 2.59/1.40  tff(c_648, plain, (~r1_xboole_0(k1_relat_1(k1_xboole_0), '#skF_1') | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_418, c_630])).
% 2.59/1.40  tff(c_656, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_553, c_18, c_648])).
% 2.59/1.40  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_417, c_656])).
% 2.59/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  Inference rules
% 2.59/1.40  ----------------------
% 2.59/1.40  #Ref     : 0
% 2.59/1.40  #Sup     : 140
% 2.59/1.40  #Fact    : 0
% 2.59/1.40  #Define  : 0
% 2.59/1.40  #Split   : 3
% 2.59/1.40  #Chain   : 0
% 2.59/1.40  #Close   : 0
% 2.59/1.40  
% 2.59/1.40  Ordering : KBO
% 2.59/1.40  
% 2.59/1.40  Simplification rules
% 2.59/1.40  ----------------------
% 2.59/1.40  #Subsume      : 10
% 2.59/1.40  #Demod        : 51
% 2.59/1.40  #Tautology    : 69
% 2.59/1.40  #SimpNegUnit  : 4
% 2.59/1.40  #BackRed      : 0
% 2.59/1.40  
% 2.59/1.40  #Partial instantiations: 0
% 2.59/1.40  #Strategies tried      : 1
% 2.59/1.40  
% 2.59/1.40  Timing (in seconds)
% 2.59/1.40  ----------------------
% 2.59/1.40  Preprocessing        : 0.32
% 2.59/1.40  Parsing              : 0.18
% 2.59/1.40  CNF conversion       : 0.02
% 2.59/1.40  Main loop            : 0.28
% 2.59/1.40  Inferencing          : 0.11
% 2.59/1.40  Reduction            : 0.08
% 2.59/1.40  Demodulation         : 0.06
% 2.59/1.40  BG Simplification    : 0.02
% 2.59/1.40  Subsumption          : 0.05
% 2.59/1.40  Abstraction          : 0.02
% 2.59/1.40  MUC search           : 0.00
% 2.59/1.40  Cooper               : 0.00
% 2.59/1.40  Total                : 0.63
% 2.59/1.40  Index Insertion      : 0.00
% 2.59/1.40  Index Deletion       : 0.00
% 2.59/1.40  Index Matching       : 0.00
% 2.59/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
