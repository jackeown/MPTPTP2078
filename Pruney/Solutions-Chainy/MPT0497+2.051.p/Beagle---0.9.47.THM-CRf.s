%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 140 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_48,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_163,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_42])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_738,plain,(
    ! [B_86,A_87] :
      ( k3_xboole_0(k1_relat_1(B_86),A_87) = k1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_84,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),k4_xboole_0(B_32,A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [B_32] : k4_xboole_0(B_32,B_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_12])).

tff(c_180,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_180])).

tff(c_557,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_595,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_557])).

tff(c_605,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_595])).

tff(c_747,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_605])).

tff(c_778,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_747])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1646,plain,(
    ! [A_117,B_118] :
      ( k1_relat_1(k7_relat_1(A_117,B_118)) != k1_xboole_0
      | k7_relat_1(A_117,B_118) = k1_xboole_0
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_26,c_152])).

tff(c_1655,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_1646])).

tff(c_1664,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1655])).

tff(c_1666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_1664])).

tff(c_1667,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1686,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_42])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( k3_xboole_0(k1_relat_1(B_25),A_24) = k1_relat_1(k7_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1891,plain,(
    ! [A_142,B_143] : k4_xboole_0(A_142,k4_xboole_0(A_142,B_143)) = k3_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2899,plain,(
    ! [A_192,B_193] : k4_xboole_0(A_192,k3_xboole_0(A_192,B_193)) = k3_xboole_0(A_192,k4_xboole_0(A_192,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1891,c_8])).

tff(c_13796,plain,(
    ! [B_407,A_408] :
      ( k4_xboole_0(k1_relat_1(B_407),k1_relat_1(k7_relat_1(B_407,A_408))) = k3_xboole_0(k1_relat_1(B_407),k4_xboole_0(k1_relat_1(B_407),A_408))
      | ~ v1_relat_1(B_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2899])).

tff(c_14066,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) = k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1667,c_13796])).

tff(c_14096,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_30,c_14066])).

tff(c_14204,plain,
    ( k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14096,c_38])).

tff(c_14235,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14204])).

tff(c_1976,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_147,A_148)),A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1992,plain,(
    ! [B_147,B_2,C_3] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_147,k4_xboole_0(B_2,C_3))),C_3)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_1976,c_2])).

tff(c_14600,plain,
    ( r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14235,c_1992])).

tff(c_14643,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14600])).

tff(c_14645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_14643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.78  
% 7.51/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.78  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.51/2.78  
% 7.51/2.78  %Foreground sorts:
% 7.51/2.78  
% 7.51/2.78  
% 7.51/2.78  %Background operators:
% 7.51/2.78  
% 7.51/2.78  
% 7.51/2.78  %Foreground operators:
% 7.51/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.51/2.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.51/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.51/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.51/2.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.51/2.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.51/2.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.51/2.78  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.78  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.51/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.51/2.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.51/2.78  
% 7.51/2.79  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 7.51/2.79  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 7.51/2.79  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 7.51/2.79  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.51/2.79  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.51/2.79  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.51/2.79  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.51/2.79  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.51/2.79  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.51/2.79  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.51/2.79  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.51/2.79  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.51/2.79  tff(c_48, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.51/2.79  tff(c_83, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 7.51/2.79  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.51/2.79  tff(c_163, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_83, c_42])).
% 7.51/2.79  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.51/2.79  tff(c_738, plain, (![B_86, A_87]: (k3_xboole_0(k1_relat_1(B_86), A_87)=k1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.51/2.79  tff(c_84, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), k4_xboole_0(B_32, A_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.51/2.79  tff(c_12, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.51/2.79  tff(c_95, plain, (![B_32]: (k4_xboole_0(B_32, B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_12])).
% 7.51/2.79  tff(c_180, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.51/2.79  tff(c_203, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_83, c_180])).
% 7.51/2.79  tff(c_557, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.79  tff(c_595, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_203, c_557])).
% 7.51/2.79  tff(c_605, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_595])).
% 7.51/2.79  tff(c_747, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_738, c_605])).
% 7.51/2.79  tff(c_778, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_747])).
% 7.51/2.79  tff(c_26, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.51/2.79  tff(c_152, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.51/2.79  tff(c_1646, plain, (![A_117, B_118]: (k1_relat_1(k7_relat_1(A_117, B_118))!=k1_xboole_0 | k7_relat_1(A_117, B_118)=k1_xboole_0 | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_26, c_152])).
% 7.51/2.79  tff(c_1655, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_778, c_1646])).
% 7.51/2.79  tff(c_1664, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1655])).
% 7.51/2.79  tff(c_1666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_1664])).
% 7.51/2.79  tff(c_1667, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 7.51/2.79  tff(c_1686, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_42])).
% 7.51/2.79  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.51/2.79  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.51/2.79  tff(c_38, plain, (![B_25, A_24]: (k3_xboole_0(k1_relat_1(B_25), A_24)=k1_relat_1(k7_relat_1(B_25, A_24)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.51/2.79  tff(c_1891, plain, (![A_142, B_143]: (k4_xboole_0(A_142, k4_xboole_0(A_142, B_143))=k3_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.79  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.79  tff(c_2899, plain, (![A_192, B_193]: (k4_xboole_0(A_192, k3_xboole_0(A_192, B_193))=k3_xboole_0(A_192, k4_xboole_0(A_192, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_1891, c_8])).
% 7.51/2.79  tff(c_13796, plain, (![B_407, A_408]: (k4_xboole_0(k1_relat_1(B_407), k1_relat_1(k7_relat_1(B_407, A_408)))=k3_xboole_0(k1_relat_1(B_407), k4_xboole_0(k1_relat_1(B_407), A_408)) | ~v1_relat_1(B_407))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2899])).
% 7.51/2.79  tff(c_14066, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))=k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1667, c_13796])).
% 7.51/2.79  tff(c_14096, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_30, c_14066])).
% 7.51/2.79  tff(c_14204, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14096, c_38])).
% 7.51/2.79  tff(c_14235, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14204])).
% 7.51/2.79  tff(c_1976, plain, (![B_147, A_148]: (r1_tarski(k1_relat_1(k7_relat_1(B_147, A_148)), A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.51/2.79  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.79  tff(c_1992, plain, (![B_147, B_2, C_3]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_147, k4_xboole_0(B_2, C_3))), C_3) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_1976, c_2])).
% 7.51/2.79  tff(c_14600, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14235, c_1992])).
% 7.51/2.79  tff(c_14643, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14600])).
% 7.51/2.79  tff(c_14645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1686, c_14643])).
% 7.51/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.79  
% 7.51/2.79  Inference rules
% 7.51/2.79  ----------------------
% 7.51/2.79  #Ref     : 0
% 7.51/2.79  #Sup     : 3528
% 7.51/2.79  #Fact    : 0
% 7.51/2.79  #Define  : 0
% 7.51/2.79  #Split   : 7
% 7.51/2.79  #Chain   : 0
% 7.51/2.79  #Close   : 0
% 7.51/2.79  
% 7.51/2.79  Ordering : KBO
% 7.51/2.79  
% 7.51/2.79  Simplification rules
% 7.51/2.79  ----------------------
% 7.51/2.79  #Subsume      : 760
% 7.51/2.79  #Demod        : 4031
% 7.51/2.79  #Tautology    : 1817
% 7.51/2.79  #SimpNegUnit  : 5
% 7.51/2.79  #BackRed      : 18
% 7.51/2.79  
% 7.51/2.79  #Partial instantiations: 0
% 7.51/2.79  #Strategies tried      : 1
% 7.51/2.79  
% 7.51/2.79  Timing (in seconds)
% 7.51/2.79  ----------------------
% 7.51/2.80  Preprocessing        : 0.31
% 7.51/2.80  Parsing              : 0.17
% 7.51/2.80  CNF conversion       : 0.02
% 7.51/2.80  Main loop            : 1.73
% 7.51/2.80  Inferencing          : 0.53
% 7.51/2.80  Reduction            : 0.69
% 7.51/2.80  Demodulation         : 0.54
% 7.51/2.80  BG Simplification    : 0.05
% 7.51/2.80  Subsumption          : 0.35
% 7.51/2.80  Abstraction          : 0.09
% 7.51/2.80  MUC search           : 0.00
% 7.51/2.80  Cooper               : 0.00
% 7.51/2.80  Total                : 2.07
% 7.51/2.80  Index Insertion      : 0.00
% 7.51/2.80  Index Deletion       : 0.00
% 7.51/2.80  Index Matching       : 0.00
% 7.51/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
