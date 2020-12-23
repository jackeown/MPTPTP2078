%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   80 (  94 expanded)
%              Number of leaves         :   41 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 128 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_139,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_221,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden(k4_tarski(A_85,B_86),C_87)
      | ~ r2_hidden(B_86,k11_relat_1(C_87,A_85))
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_45,C_47,B_46] :
      ( r2_hidden(A_45,k1_relat_1(C_47))
      | ~ r2_hidden(k4_tarski(A_45,B_46),C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_252,plain,(
    ! [A_94,C_95,B_96] :
      ( r2_hidden(A_94,k1_relat_1(C_95))
      | ~ r2_hidden(B_96,k11_relat_1(C_95,A_94))
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_221,c_50])).

tff(c_261,plain,(
    ! [A_97,C_98] :
      ( r2_hidden(A_97,k1_relat_1(C_98))
      | ~ v1_relat_1(C_98)
      | k11_relat_1(C_98,A_97) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_252])).

tff(c_276,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_111])).

tff(c_282,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_276])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_282])).

tff(c_286,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_42,plain,(
    ! [A_41] :
      ( k10_relat_1(A_41,k2_relat_1(A_41)) = k1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_100,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_97])).

tff(c_320,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_329,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_320])).

tff(c_332,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_329])).

tff(c_26,plain,(
    ! [B_31] : k4_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) != k1_tarski(B_31) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_333,plain,(
    ! [B_31] : k1_tarski(B_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_26])).

tff(c_292,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k1_tarski(A_101),B_102)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_301,plain,(
    ! [A_101] :
      ( k1_tarski(A_101) = k1_xboole_0
      | ~ r2_hidden(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_292,c_6])).

tff(c_341,plain,(
    ! [A_101] : ~ r2_hidden(A_101,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_301])).

tff(c_285,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_600,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_hidden(k4_tarski(A_173,'#skF_2'(A_173,B_174,C_175)),C_175)
      | ~ r2_hidden(A_173,k10_relat_1(C_175,B_174))
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [B_43,C_44,A_42] :
      ( r2_hidden(B_43,k11_relat_1(C_44,A_42))
      | ~ r2_hidden(k4_tarski(A_42,B_43),C_44)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_725,plain,(
    ! [A_186,B_187,C_188] :
      ( r2_hidden('#skF_2'(A_186,B_187,C_188),k11_relat_1(C_188,A_186))
      | ~ r2_hidden(A_186,k10_relat_1(C_188,B_187))
      | ~ v1_relat_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_600,c_46])).

tff(c_737,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_187))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_725])).

tff(c_742,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_737])).

tff(c_775,plain,(
    ! [B_193] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_193)) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_742])).

tff(c_785,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_775])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_286,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:28:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.42  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.90/1.42  
% 2.90/1.42  %Foreground sorts:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Background operators:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Foreground operators:
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.90/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.90/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.90/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.90/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.90/1.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.90/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.90/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.90/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.90/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.90/1.42  
% 2.90/1.43  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.90/1.43  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.90/1.43  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.90/1.43  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.90/1.43  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.90/1.43  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.90/1.43  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.90/1.43  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.43  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.90/1.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.90/1.43  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.90/1.43  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.90/1.43  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.90/1.43  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.90/1.43  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.43  tff(c_54, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.43  tff(c_111, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.90/1.43  tff(c_60, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.43  tff(c_139, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_111, c_60])).
% 2.90/1.43  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.43  tff(c_221, plain, (![A_85, B_86, C_87]: (r2_hidden(k4_tarski(A_85, B_86), C_87) | ~r2_hidden(B_86, k11_relat_1(C_87, A_85)) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.90/1.43  tff(c_50, plain, (![A_45, C_47, B_46]: (r2_hidden(A_45, k1_relat_1(C_47)) | ~r2_hidden(k4_tarski(A_45, B_46), C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.43  tff(c_252, plain, (![A_94, C_95, B_96]: (r2_hidden(A_94, k1_relat_1(C_95)) | ~r2_hidden(B_96, k11_relat_1(C_95, A_94)) | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_221, c_50])).
% 2.90/1.43  tff(c_261, plain, (![A_97, C_98]: (r2_hidden(A_97, k1_relat_1(C_98)) | ~v1_relat_1(C_98) | k11_relat_1(C_98, A_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_252])).
% 2.90/1.43  tff(c_276, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_111])).
% 2.90/1.43  tff(c_282, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_276])).
% 2.90/1.43  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_282])).
% 2.90/1.43  tff(c_286, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 2.90/1.43  tff(c_42, plain, (![A_41]: (k10_relat_1(A_41, k2_relat_1(A_41))=k1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.43  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.43  tff(c_30, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.90/1.43  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.43  tff(c_88, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.43  tff(c_97, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 2.90/1.43  tff(c_100, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_97])).
% 2.90/1.43  tff(c_320, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.43  tff(c_329, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_100, c_320])).
% 2.90/1.43  tff(c_332, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_329])).
% 2.90/1.43  tff(c_26, plain, (![B_31]: (k4_xboole_0(k1_tarski(B_31), k1_tarski(B_31))!=k1_tarski(B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.43  tff(c_333, plain, (![B_31]: (k1_tarski(B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_26])).
% 2.90/1.43  tff(c_292, plain, (![A_101, B_102]: (r1_tarski(k1_tarski(A_101), B_102) | ~r2_hidden(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.43  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.43  tff(c_301, plain, (![A_101]: (k1_tarski(A_101)=k1_xboole_0 | ~r2_hidden(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_292, c_6])).
% 2.90/1.43  tff(c_341, plain, (![A_101]: (~r2_hidden(A_101, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_333, c_301])).
% 2.90/1.43  tff(c_285, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.90/1.43  tff(c_600, plain, (![A_173, B_174, C_175]: (r2_hidden(k4_tarski(A_173, '#skF_2'(A_173, B_174, C_175)), C_175) | ~r2_hidden(A_173, k10_relat_1(C_175, B_174)) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.90/1.43  tff(c_46, plain, (![B_43, C_44, A_42]: (r2_hidden(B_43, k11_relat_1(C_44, A_42)) | ~r2_hidden(k4_tarski(A_42, B_43), C_44) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.90/1.43  tff(c_725, plain, (![A_186, B_187, C_188]: (r2_hidden('#skF_2'(A_186, B_187, C_188), k11_relat_1(C_188, A_186)) | ~r2_hidden(A_186, k10_relat_1(C_188, B_187)) | ~v1_relat_1(C_188))), inference(resolution, [status(thm)], [c_600, c_46])).
% 2.90/1.43  tff(c_737, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_187)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_725])).
% 2.90/1.43  tff(c_742, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_187)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_737])).
% 2.90/1.43  tff(c_775, plain, (![B_193]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_193)))), inference(negUnitSimplification, [status(thm)], [c_341, c_742])).
% 2.90/1.43  tff(c_785, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_775])).
% 2.90/1.43  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_286, c_785])).
% 2.90/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.43  
% 2.90/1.43  Inference rules
% 2.90/1.43  ----------------------
% 2.90/1.43  #Ref     : 0
% 2.90/1.43  #Sup     : 152
% 2.90/1.43  #Fact    : 0
% 2.90/1.43  #Define  : 0
% 2.90/1.43  #Split   : 3
% 2.90/1.43  #Chain   : 0
% 2.90/1.43  #Close   : 0
% 2.90/1.43  
% 2.90/1.43  Ordering : KBO
% 2.90/1.43  
% 2.90/1.43  Simplification rules
% 2.90/1.43  ----------------------
% 2.90/1.43  #Subsume      : 21
% 2.90/1.43  #Demod        : 31
% 2.90/1.43  #Tautology    : 66
% 2.90/1.43  #SimpNegUnit  : 9
% 2.90/1.43  #BackRed      : 4
% 2.90/1.43  
% 2.90/1.43  #Partial instantiations: 0
% 2.90/1.43  #Strategies tried      : 1
% 2.90/1.43  
% 2.90/1.43  Timing (in seconds)
% 2.90/1.43  ----------------------
% 2.90/1.44  Preprocessing        : 0.33
% 2.90/1.44  Parsing              : 0.17
% 2.90/1.44  CNF conversion       : 0.02
% 2.90/1.44  Main loop            : 0.32
% 2.90/1.44  Inferencing          : 0.13
% 2.90/1.44  Reduction            : 0.08
% 2.90/1.44  Demodulation         : 0.06
% 2.90/1.44  BG Simplification    : 0.02
% 2.90/1.44  Subsumption          : 0.06
% 2.90/1.44  Abstraction          : 0.02
% 2.90/1.44  MUC search           : 0.00
% 2.90/1.44  Cooper               : 0.00
% 2.90/1.44  Total                : 0.68
% 2.90/1.44  Index Insertion      : 0.00
% 2.90/1.44  Index Deletion       : 0.00
% 2.90/1.44  Index Matching       : 0.00
% 2.90/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
