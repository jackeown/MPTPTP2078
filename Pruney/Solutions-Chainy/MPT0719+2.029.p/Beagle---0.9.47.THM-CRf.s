%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 171 expanded)
%              Number of leaves         :   41 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 266 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_329,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k3_xboole_0(A_119,B_120)) = k4_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_338,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_329])).

tff(c_342,plain,(
    ! [A_121] : k4_xboole_0(A_121,A_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_30,plain,(
    ! [C_41,B_40] : ~ r2_hidden(C_41,k4_xboole_0(B_40,k1_tarski(C_41))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_347,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_30])).

tff(c_42,plain,(
    ! [A_62] :
      ( v1_xboole_0(k1_relat_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_85,plain,(
    ! [A_81] :
      ( v1_xboole_0(k1_relat_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_83] :
      ( k1_relat_1(A_83) = k1_xboole_0
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_117,plain,(
    ! [A_90] :
      ( k1_relat_1(k1_relat_1(A_90)) = k1_xboole_0
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_100,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_2'(A_84),A_84)
      | v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(A_85)
      | v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_109,plain,(
    ! [A_62] :
      ( v1_relat_1(k1_relat_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_42,c_105])).

tff(c_126,plain,(
    ! [A_90] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_90))
      | ~ v1_xboole_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_109])).

tff(c_174,plain,(
    ! [A_99] :
      ( ~ v1_xboole_0(k1_relat_1(A_99))
      | ~ v1_xboole_0(A_99) ) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_181,plain,(
    ! [A_62] : ~ v1_xboole_0(A_62) ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_4])).

tff(c_187,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_209,plain,(
    ! [A_107] : k4_xboole_0(A_107,A_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_196])).

tff(c_219,plain,(
    ! [C_108] : ~ r2_hidden(C_108,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_30])).

tff(c_228,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_182,c_219])).

tff(c_229,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_132,plain,(
    ! [A_90] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_90))
      | ~ v1_xboole_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_42])).

tff(c_231,plain,(
    ! [A_109] :
      ( ~ v1_xboole_0(k1_relat_1(A_109))
      | ~ v1_xboole_0(A_109) ) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_238,plain,(
    ! [A_62] : ~ v1_xboole_0(A_62) ),
    inference(resolution,[status(thm)],[c_42,c_231])).

tff(c_252,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_4])).

tff(c_239,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_239])).

tff(c_256,plain,(
    ! [A_114] : k4_xboole_0(A_114,A_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_248])).

tff(c_275,plain,(
    ! [C_118] : ~ r2_hidden(C_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_30])).

tff(c_284,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_252,c_275])).

tff(c_285,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_44,plain,(
    ! [A_63] :
      ( v1_funct_1(A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_301,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_285,c_44])).

tff(c_93,plain,(
    ! [A_81] :
      ( k1_relat_1(A_81) = k1_xboole_0
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_300,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_285,c_93])).

tff(c_755,plain,(
    ! [A_186,B_187] :
      ( r2_hidden('#skF_5'(A_186,B_187),k1_relat_1(B_187))
      | v5_funct_1(B_187,A_186)
      | ~ v1_funct_1(B_187)
      | ~ v1_relat_1(B_187)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_764,plain,(
    ! [A_186] :
      ( r2_hidden('#skF_5'(A_186,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_186)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_755])).

tff(c_771,plain,(
    ! [A_186] :
      ( r2_hidden('#skF_5'(A_186,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_186)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_301,c_764])).

tff(c_774,plain,(
    ! [A_188] :
      ( v5_funct_1(k1_xboole_0,A_188)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_771])).

tff(c_52,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_777,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_774,c_52])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:01:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.52  
% 2.98/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.52  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 2.98/1.52  
% 2.98/1.52  %Foreground sorts:
% 2.98/1.52  
% 2.98/1.52  
% 2.98/1.52  %Background operators:
% 2.98/1.52  
% 2.98/1.52  
% 2.98/1.52  %Foreground operators:
% 2.98/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.98/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.98/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.52  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.98/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.98/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.98/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.98/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.52  
% 2.98/1.54  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.98/1.54  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.98/1.54  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.98/1.54  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.98/1.54  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.98/1.54  tff(f_78, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.98/1.54  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.98/1.54  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.98/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.98/1.54  tff(f_82, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.98/1.54  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.98/1.54  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.98/1.54  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.98/1.54  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.54  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.54  tff(c_329, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k3_xboole_0(A_119, B_120))=k4_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.54  tff(c_338, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_329])).
% 2.98/1.54  tff(c_342, plain, (![A_121]: (k4_xboole_0(A_121, A_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_338])).
% 2.98/1.54  tff(c_30, plain, (![C_41, B_40]: (~r2_hidden(C_41, k4_xboole_0(B_40, k1_tarski(C_41))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.98/1.54  tff(c_347, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_342, c_30])).
% 2.98/1.54  tff(c_42, plain, (![A_62]: (v1_xboole_0(k1_relat_1(A_62)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.54  tff(c_85, plain, (![A_81]: (v1_xboole_0(k1_relat_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.54  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.54  tff(c_95, plain, (![A_83]: (k1_relat_1(A_83)=k1_xboole_0 | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_85, c_8])).
% 2.98/1.54  tff(c_117, plain, (![A_90]: (k1_relat_1(k1_relat_1(A_90))=k1_xboole_0 | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_42, c_95])).
% 2.98/1.54  tff(c_100, plain, (![A_84]: (r2_hidden('#skF_2'(A_84), A_84) | v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.98/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.54  tff(c_105, plain, (![A_85]: (~v1_xboole_0(A_85) | v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.98/1.54  tff(c_109, plain, (![A_62]: (v1_relat_1(k1_relat_1(A_62)) | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_42, c_105])).
% 2.98/1.54  tff(c_126, plain, (![A_90]: (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_90)) | ~v1_xboole_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_117, c_109])).
% 2.98/1.54  tff(c_174, plain, (![A_99]: (~v1_xboole_0(k1_relat_1(A_99)) | ~v1_xboole_0(A_99))), inference(splitLeft, [status(thm)], [c_126])).
% 2.98/1.54  tff(c_181, plain, (![A_62]: (~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_42, c_174])).
% 2.98/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.54  tff(c_182, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_181, c_4])).
% 2.98/1.54  tff(c_187, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.54  tff(c_196, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_187])).
% 2.98/1.54  tff(c_209, plain, (![A_107]: (k4_xboole_0(A_107, A_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_196])).
% 2.98/1.54  tff(c_219, plain, (![C_108]: (~r2_hidden(C_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_209, c_30])).
% 2.98/1.54  tff(c_228, plain, $false, inference(resolution, [status(thm)], [c_182, c_219])).
% 2.98/1.54  tff(c_229, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 2.98/1.54  tff(c_132, plain, (![A_90]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_90)) | ~v1_xboole_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_117, c_42])).
% 2.98/1.54  tff(c_231, plain, (![A_109]: (~v1_xboole_0(k1_relat_1(A_109)) | ~v1_xboole_0(A_109))), inference(splitLeft, [status(thm)], [c_132])).
% 2.98/1.54  tff(c_238, plain, (![A_62]: (~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_42, c_231])).
% 2.98/1.54  tff(c_252, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_238, c_4])).
% 2.98/1.54  tff(c_239, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.54  tff(c_248, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_239])).
% 2.98/1.54  tff(c_256, plain, (![A_114]: (k4_xboole_0(A_114, A_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_248])).
% 2.98/1.54  tff(c_275, plain, (![C_118]: (~r2_hidden(C_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_30])).
% 2.98/1.54  tff(c_284, plain, $false, inference(resolution, [status(thm)], [c_252, c_275])).
% 2.98/1.54  tff(c_285, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_132])).
% 2.98/1.54  tff(c_44, plain, (![A_63]: (v1_funct_1(A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.54  tff(c_301, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_285, c_44])).
% 2.98/1.54  tff(c_93, plain, (![A_81]: (k1_relat_1(A_81)=k1_xboole_0 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_85, c_8])).
% 2.98/1.54  tff(c_300, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_285, c_93])).
% 2.98/1.54  tff(c_755, plain, (![A_186, B_187]: (r2_hidden('#skF_5'(A_186, B_187), k1_relat_1(B_187)) | v5_funct_1(B_187, A_186) | ~v1_funct_1(B_187) | ~v1_relat_1(B_187) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.98/1.54  tff(c_764, plain, (![A_186]: (r2_hidden('#skF_5'(A_186, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_186) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(superposition, [status(thm), theory('equality')], [c_300, c_755])).
% 2.98/1.54  tff(c_771, plain, (![A_186]: (r2_hidden('#skF_5'(A_186, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_186) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_301, c_764])).
% 2.98/1.54  tff(c_774, plain, (![A_188]: (v5_funct_1(k1_xboole_0, A_188) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(negUnitSimplification, [status(thm)], [c_347, c_771])).
% 2.98/1.54  tff(c_52, plain, (~v5_funct_1(k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.98/1.54  tff(c_777, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_774, c_52])).
% 2.98/1.54  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_777])).
% 2.98/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.54  
% 2.98/1.54  Inference rules
% 2.98/1.54  ----------------------
% 2.98/1.54  #Ref     : 1
% 2.98/1.54  #Sup     : 156
% 2.98/1.54  #Fact    : 0
% 2.98/1.54  #Define  : 0
% 2.98/1.54  #Split   : 2
% 2.98/1.54  #Chain   : 0
% 2.98/1.54  #Close   : 0
% 2.98/1.54  
% 2.98/1.54  Ordering : KBO
% 2.98/1.54  
% 2.98/1.54  Simplification rules
% 2.98/1.54  ----------------------
% 2.98/1.54  #Subsume      : 38
% 2.98/1.54  #Demod        : 55
% 2.98/1.54  #Tautology    : 91
% 2.98/1.54  #SimpNegUnit  : 13
% 2.98/1.54  #BackRed      : 4
% 2.98/1.54  
% 2.98/1.54  #Partial instantiations: 0
% 2.98/1.54  #Strategies tried      : 1
% 2.98/1.54  
% 2.98/1.54  Timing (in seconds)
% 2.98/1.54  ----------------------
% 2.98/1.54  Preprocessing        : 0.41
% 2.98/1.54  Parsing              : 0.21
% 2.98/1.54  CNF conversion       : 0.03
% 2.98/1.54  Main loop            : 0.32
% 2.98/1.54  Inferencing          : 0.13
% 3.14/1.54  Reduction            : 0.09
% 3.14/1.54  Demodulation         : 0.06
% 3.14/1.54  BG Simplification    : 0.02
% 3.14/1.54  Subsumption          : 0.05
% 3.14/1.54  Abstraction          : 0.02
% 3.14/1.54  MUC search           : 0.00
% 3.14/1.54  Cooper               : 0.00
% 3.14/1.55  Total                : 0.77
% 3.14/1.55  Index Insertion      : 0.00
% 3.14/1.55  Index Deletion       : 0.00
% 3.14/1.55  Index Matching       : 0.00
% 3.14/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
