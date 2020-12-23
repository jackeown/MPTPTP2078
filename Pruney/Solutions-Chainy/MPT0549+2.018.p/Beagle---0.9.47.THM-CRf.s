%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:50 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 144 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_45,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_70,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_38])).

tff(c_259,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(B_45,A_46) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_265,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_259])).

tff(c_272,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_265])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_278,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_14])).

tff(c_285,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16,c_278])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_285])).

tff(c_289,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k4_xboole_0(A_22,B_23))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_65,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_30])).

tff(c_69,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12,plain,(
    ! [A_11] : k7_relat_1(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_474,plain,(
    ! [B_65,A_66] :
      ( r1_xboole_0(k1_relat_1(B_65),A_66)
      | k7_relat_1(B_65,A_66) != k1_xboole_0
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_480,plain,(
    ! [A_66] :
      ( r1_xboole_0(k1_xboole_0,A_66)
      | k7_relat_1(k1_xboole_0,A_66) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_474])).

tff(c_485,plain,(
    ! [A_66] : r1_xboole_0(k1_xboole_0,A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12,c_480])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [A_56] :
      ( k1_relat_1(A_56) = k1_xboole_0
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_620,plain,(
    ! [A_82,B_83] :
      ( k1_relat_1(k7_relat_1(A_82,B_83)) = k1_xboole_0
      | k2_relat_1(k7_relat_1(A_82,B_83)) != k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_788,plain,(
    ! [B_96,A_97] :
      ( k1_relat_1(k7_relat_1(B_96,A_97)) = k1_xboole_0
      | k9_relat_1(B_96,A_97) != k1_xboole_0
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_620])).

tff(c_403,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( ~ r1_xboole_0(k3_xboole_0(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_416,plain,(
    ! [B_61,A_62] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(B_61,A_62)),A_62)
      | r1_xboole_0(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_6])).

tff(c_804,plain,(
    ! [A_97,B_96] :
      ( ~ r1_xboole_0(k1_xboole_0,A_97)
      | r1_xboole_0(k1_relat_1(B_96),A_97)
      | ~ v1_relat_1(B_96)
      | k9_relat_1(B_96,A_97) != k1_xboole_0
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_416])).

tff(c_838,plain,(
    ! [B_98,A_99] :
      ( r1_xboole_0(k1_relat_1(B_98),A_99)
      | k9_relat_1(B_98,A_99) != k1_xboole_0
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_804])).

tff(c_288,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_848,plain,
    ( k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_838,c_288])).

tff(c_863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_289,c_848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.68/1.42  
% 2.68/1.42  %Foreground sorts:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Background operators:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Foreground operators:
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.68/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.68/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.42  
% 2.68/1.44  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.68/1.44  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.44  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.68/1.44  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.68/1.44  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.68/1.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.68/1.44  tff(f_45, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.68/1.44  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.68/1.44  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.68/1.44  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.68/1.44  tff(f_35, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.68/1.44  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.44  tff(c_32, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.44  tff(c_70, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.68/1.44  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.44  tff(c_38, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.44  tff(c_140, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_38])).
% 2.68/1.44  tff(c_259, plain, (![B_45, A_46]: (k7_relat_1(B_45, A_46)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.44  tff(c_265, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_140, c_259])).
% 2.68/1.44  tff(c_272, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_265])).
% 2.68/1.44  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_278, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_272, c_14])).
% 2.68/1.44  tff(c_285, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16, c_278])).
% 2.68/1.44  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_285])).
% 2.68/1.44  tff(c_289, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.68/1.44  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.44  tff(c_61, plain, (![A_22, B_23]: (v1_relat_1(k4_xboole_0(A_22, B_23)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.44  tff(c_64, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 2.68/1.44  tff(c_65, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_64])).
% 2.68/1.44  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_30])).
% 2.68/1.44  tff(c_69, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_64])).
% 2.68/1.44  tff(c_12, plain, (![A_11]: (k7_relat_1(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.44  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.44  tff(c_474, plain, (![B_65, A_66]: (r1_xboole_0(k1_relat_1(B_65), A_66) | k7_relat_1(B_65, A_66)!=k1_xboole_0 | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.44  tff(c_480, plain, (![A_66]: (r1_xboole_0(k1_xboole_0, A_66) | k7_relat_1(k1_xboole_0, A_66)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_474])).
% 2.68/1.44  tff(c_485, plain, (![A_66]: (r1_xboole_0(k1_xboole_0, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12, c_480])).
% 2.68/1.44  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.44  tff(c_349, plain, (![A_56]: (k1_relat_1(A_56)=k1_xboole_0 | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.68/1.44  tff(c_620, plain, (![A_82, B_83]: (k1_relat_1(k7_relat_1(A_82, B_83))=k1_xboole_0 | k2_relat_1(k7_relat_1(A_82, B_83))!=k1_xboole_0 | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_8, c_349])).
% 2.68/1.44  tff(c_788, plain, (![B_96, A_97]: (k1_relat_1(k7_relat_1(B_96, A_97))=k1_xboole_0 | k9_relat_1(B_96, A_97)!=k1_xboole_0 | ~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_14, c_620])).
% 2.68/1.44  tff(c_403, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.68/1.44  tff(c_6, plain, (![A_5, B_6]: (~r1_xboole_0(k3_xboole_0(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.44  tff(c_416, plain, (![B_61, A_62]: (~r1_xboole_0(k1_relat_1(k7_relat_1(B_61, A_62)), A_62) | r1_xboole_0(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_403, c_6])).
% 2.68/1.44  tff(c_804, plain, (![A_97, B_96]: (~r1_xboole_0(k1_xboole_0, A_97) | r1_xboole_0(k1_relat_1(B_96), A_97) | ~v1_relat_1(B_96) | k9_relat_1(B_96, A_97)!=k1_xboole_0 | ~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_788, c_416])).
% 2.68/1.44  tff(c_838, plain, (![B_98, A_99]: (r1_xboole_0(k1_relat_1(B_98), A_99) | k9_relat_1(B_98, A_99)!=k1_xboole_0 | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_804])).
% 2.68/1.44  tff(c_288, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.68/1.44  tff(c_848, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_838, c_288])).
% 2.68/1.44  tff(c_863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_289, c_848])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 0
% 2.68/1.44  #Sup     : 197
% 2.68/1.44  #Fact    : 0
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 4
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 13
% 2.68/1.44  #Demod        : 144
% 2.68/1.44  #Tautology    : 104
% 2.68/1.44  #SimpNegUnit  : 7
% 2.68/1.44  #BackRed      : 1
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 0
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.44  Preprocessing        : 0.30
% 2.68/1.44  Parsing              : 0.16
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.37
% 2.68/1.44  Inferencing          : 0.15
% 2.68/1.44  Reduction            : 0.11
% 2.68/1.44  Demodulation         : 0.08
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.06
% 2.68/1.44  Abstraction          : 0.02
% 2.68/1.44  MUC search           : 0.00
% 2.68/1.44  Cooper               : 0.00
% 2.68/1.44  Total                : 0.70
% 2.68/1.44  Index Insertion      : 0.00
% 2.68/1.44  Index Deletion       : 0.00
% 2.68/1.44  Index Matching       : 0.00
% 2.68/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
