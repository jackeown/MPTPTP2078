%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:39 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 190 expanded)
%              Number of equality atoms :   48 ( 110 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_588,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(A_80,B_81)
      | k4_xboole_0(A_80,B_81) != A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_169,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_194,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_357,plain,(
    ! [B_66,A_67] :
      ( k3_xboole_0(k1_relat_1(B_66),A_67) = k1_relat_1(k7_relat_1(B_66,A_67))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_247,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_268,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_247])).

tff(c_271,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_268])).

tff(c_184,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_169,c_184])).

tff(c_265,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_247])).

tff(c_345,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_265])).

tff(c_363,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_345])).

tff(c_394,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_363])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k7_relat_1(A_34,B_35))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [B_38,A_37] :
      ( k3_xboole_0(k1_relat_1(B_38),A_37) = k1_relat_1(k7_relat_1(B_38,A_37))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_401,plain,(
    ! [A_37] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_37)) = k3_xboole_0(k1_xboole_0,A_37)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_40])).

tff(c_517,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_520,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_517])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_520])).

tff(c_526,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_38,plain,(
    ! [A_36] :
      ( k1_relat_1(A_36) != k1_xboole_0
      | k1_xboole_0 = A_36
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_529,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_526,c_38])).

tff(c_535,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_529])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_535])).

tff(c_539,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_592,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_539])).

tff(c_84,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_538,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_712,plain,(
    ! [B_97,A_98] :
      ( k3_xboole_0(k1_relat_1(B_97),A_98) = k1_relat_1(k7_relat_1(B_97,A_98))
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1462,plain,(
    ! [B_139,A_140] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_139,A_140)),k4_xboole_0(k1_relat_1(B_139),A_140)) = k1_relat_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_12])).

tff(c_1520,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_1462])).

tff(c_1549,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_100,c_34,c_1520])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_1549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.58  
% 3.15/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.58  %$ r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.15/1.58  
% 3.15/1.58  %Foreground sorts:
% 3.15/1.58  
% 3.15/1.58  
% 3.15/1.58  %Background operators:
% 3.15/1.58  
% 3.15/1.58  
% 3.15/1.58  %Foreground operators:
% 3.15/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.15/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.58  
% 3.15/1.59  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.15/1.59  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.15/1.59  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.15/1.59  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.15/1.59  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.59  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.59  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.15/1.59  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.15/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.15/1.59  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.15/1.59  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.59  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.15/1.59  tff(c_588, plain, (![A_80, B_81]: (r1_xboole_0(A_80, B_81) | k4_xboole_0(A_80, B_81)!=A_80)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.59  tff(c_50, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.59  tff(c_169, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.15/1.59  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.59  tff(c_194, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_44])).
% 3.15/1.59  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.59  tff(c_357, plain, (![B_66, A_67]: (k3_xboole_0(k1_relat_1(B_66), A_67)=k1_relat_1(k7_relat_1(B_66, A_67)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.59  tff(c_6, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.59  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.59  tff(c_247, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.59  tff(c_268, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_247])).
% 3.15/1.59  tff(c_271, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_268])).
% 3.15/1.59  tff(c_184, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.59  tff(c_192, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_169, c_184])).
% 3.15/1.59  tff(c_265, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_192, c_247])).
% 3.15/1.59  tff(c_345, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_271, c_265])).
% 3.15/1.59  tff(c_363, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_357, c_345])).
% 3.15/1.59  tff(c_394, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_363])).
% 3.15/1.59  tff(c_30, plain, (![A_34, B_35]: (v1_relat_1(k7_relat_1(A_34, B_35)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.59  tff(c_40, plain, (![B_38, A_37]: (k3_xboole_0(k1_relat_1(B_38), A_37)=k1_relat_1(k7_relat_1(B_38, A_37)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.59  tff(c_401, plain, (![A_37]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_37))=k3_xboole_0(k1_xboole_0, A_37) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_394, c_40])).
% 3.15/1.59  tff(c_517, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_401])).
% 3.15/1.59  tff(c_520, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_517])).
% 3.15/1.59  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_520])).
% 3.15/1.59  tff(c_526, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_401])).
% 3.15/1.59  tff(c_38, plain, (![A_36]: (k1_relat_1(A_36)!=k1_xboole_0 | k1_xboole_0=A_36 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.59  tff(c_529, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_526, c_38])).
% 3.15/1.59  tff(c_535, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_394, c_529])).
% 3.15/1.59  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_535])).
% 3.15/1.59  tff(c_539, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.59  tff(c_592, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_588, c_539])).
% 3.15/1.59  tff(c_84, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.59  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.59  tff(c_100, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_84, c_4])).
% 3.15/1.59  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.59  tff(c_538, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.59  tff(c_712, plain, (![B_97, A_98]: (k3_xboole_0(k1_relat_1(B_97), A_98)=k1_relat_1(k7_relat_1(B_97, A_98)) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.59  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.59  tff(c_1462, plain, (![B_139, A_140]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_139, A_140)), k4_xboole_0(k1_relat_1(B_139), A_140))=k1_relat_1(B_139) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_712, c_12])).
% 3.15/1.59  tff(c_1520, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_538, c_1462])).
% 3.15/1.59  tff(c_1549, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_100, c_34, c_1520])).
% 3.15/1.59  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_1549])).
% 3.15/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.59  
% 3.15/1.59  Inference rules
% 3.15/1.59  ----------------------
% 3.15/1.59  #Ref     : 0
% 3.15/1.59  #Sup     : 355
% 3.15/1.59  #Fact    : 0
% 3.15/1.59  #Define  : 0
% 3.15/1.59  #Split   : 7
% 3.15/1.59  #Chain   : 0
% 3.15/1.59  #Close   : 0
% 3.15/1.59  
% 3.15/1.59  Ordering : KBO
% 3.15/1.59  
% 3.15/1.59  Simplification rules
% 3.15/1.59  ----------------------
% 3.15/1.59  #Subsume      : 17
% 3.15/1.59  #Demod        : 335
% 3.15/1.59  #Tautology    : 236
% 3.15/1.59  #SimpNegUnit  : 2
% 3.15/1.59  #BackRed      : 1
% 3.15/1.59  
% 3.15/1.59  #Partial instantiations: 0
% 3.15/1.59  #Strategies tried      : 1
% 3.15/1.59  
% 3.15/1.59  Timing (in seconds)
% 3.15/1.59  ----------------------
% 3.15/1.60  Preprocessing        : 0.34
% 3.15/1.60  Parsing              : 0.18
% 3.15/1.60  CNF conversion       : 0.02
% 3.15/1.60  Main loop            : 0.43
% 3.15/1.60  Inferencing          : 0.15
% 3.15/1.60  Reduction            : 0.16
% 3.15/1.60  Demodulation         : 0.12
% 3.15/1.60  BG Simplification    : 0.02
% 3.15/1.60  Subsumption          : 0.07
% 3.15/1.60  Abstraction          : 0.03
% 3.15/1.60  MUC search           : 0.00
% 3.15/1.60  Cooper               : 0.00
% 3.15/1.60  Total                : 0.80
% 3.15/1.60  Index Insertion      : 0.00
% 3.15/1.60  Index Deletion       : 0.00
% 3.15/1.60  Index Matching       : 0.00
% 3.15/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
