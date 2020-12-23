%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 126 expanded)
%              Number of leaves         :   44 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 186 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_231,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_240,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_244,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_240])).

tff(c_38,plain,(
    ! [C_42,B_41] : ~ r2_hidden(C_42,k4_xboole_0(B_41,k1_tarski(C_42))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_249,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_38])).

tff(c_48,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_254,plain,(
    ! [C_106] : ~ r2_hidden(C_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_38])).

tff(c_259,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_254])).

tff(c_10,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [A_63] :
      ( v1_xboole_0(k1_relat_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_91,plain,(
    ! [A_81] :
      ( v1_xboole_0(k1_relat_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_84] :
      ( k1_relat_1(A_84) = k1_xboole_0
      | ~ v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_117,plain,(
    ! [A_88] :
      ( k1_relat_1(k1_relat_1(A_88)) = k1_xboole_0
      | ~ v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_50,c_110])).

tff(c_129,plain,(
    ! [A_88] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_88))
      | ~ v1_xboole_0(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_50])).

tff(c_171,plain,(
    ! [A_97] :
      ( ~ v1_xboole_0(k1_relat_1(A_97))
      | ~ v1_xboole_0(A_97) ) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_178,plain,(
    ! [A_63] : ~ v1_xboole_0(A_63) ),
    inference(resolution,[status(thm)],[c_50,c_171])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( ~ r1_xboole_0(B_10,A_9)
      | ~ r1_tarski(B_10,A_9)
      | v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    ! [B_99,A_100] :
      ( ~ r1_xboole_0(B_99,A_100)
      | ~ r1_tarski(B_99,A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_18])).

tff(c_185,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_190,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_52,plain,(
    ! [A_64] :
      ( v1_funct_1(A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_201,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_190,c_52])).

tff(c_99,plain,(
    ! [A_81] :
      ( k1_relat_1(A_81) = k1_xboole_0
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_200,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_99])).

tff(c_425,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_4'(A_160,B_161),k1_relat_1(B_161))
      | v5_funct_1(B_161,A_160)
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_428,plain,(
    ! [A_160] :
      ( r2_hidden('#skF_4'(A_160,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_160)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_425])).

tff(c_433,plain,(
    ! [A_160] :
      ( r2_hidden('#skF_4'(A_160,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_160)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_201,c_428])).

tff(c_436,plain,(
    ! [A_162] :
      ( v5_funct_1(k1_xboole_0,A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_433])).

tff(c_60,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_439,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_436,c_60])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:07 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  
% 2.30/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.30/1.36  
% 2.30/1.36  %Foreground sorts:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Background operators:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Foreground operators:
% 2.30/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.30/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.36  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.30/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.30/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.36  
% 2.63/1.37  tff(f_125, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.63/1.37  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.63/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.63/1.37  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.63/1.37  tff(f_82, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.63/1.37  tff(f_94, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.63/1.37  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.37  tff(f_51, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.63/1.37  tff(f_98, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.63/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.63/1.37  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.63/1.37  tff(f_102, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.63/1.37  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.63/1.37  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.63/1.37  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.63/1.37  tff(c_20, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.37  tff(c_231, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.37  tff(c_240, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_231])).
% 2.63/1.37  tff(c_244, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_240])).
% 2.63/1.37  tff(c_38, plain, (![C_42, B_41]: (~r2_hidden(C_42, k4_xboole_0(B_41, k1_tarski(C_42))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.63/1.37  tff(c_249, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_38])).
% 2.63/1.37  tff(c_48, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_254, plain, (![C_106]: (~r2_hidden(C_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_38])).
% 2.63/1.37  tff(c_259, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_254])).
% 2.63/1.37  tff(c_10, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.37  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.37  tff(c_50, plain, (![A_63]: (v1_xboole_0(k1_relat_1(A_63)) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.37  tff(c_91, plain, (![A_81]: (v1_xboole_0(k1_relat_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.37  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.37  tff(c_110, plain, (![A_84]: (k1_relat_1(A_84)=k1_xboole_0 | ~v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_91, c_4])).
% 2.63/1.37  tff(c_117, plain, (![A_88]: (k1_relat_1(k1_relat_1(A_88))=k1_xboole_0 | ~v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_50, c_110])).
% 2.63/1.37  tff(c_129, plain, (![A_88]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_88)) | ~v1_xboole_0(A_88))), inference(superposition, [status(thm), theory('equality')], [c_117, c_50])).
% 2.63/1.37  tff(c_171, plain, (![A_97]: (~v1_xboole_0(k1_relat_1(A_97)) | ~v1_xboole_0(A_97))), inference(splitLeft, [status(thm)], [c_129])).
% 2.63/1.37  tff(c_178, plain, (![A_63]: (~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_50, c_171])).
% 2.63/1.37  tff(c_18, plain, (![B_10, A_9]: (~r1_xboole_0(B_10, A_9) | ~r1_tarski(B_10, A_9) | v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.37  tff(c_182, plain, (![B_99, A_100]: (~r1_xboole_0(B_99, A_100) | ~r1_tarski(B_99, A_100))), inference(negUnitSimplification, [status(thm)], [c_178, c_18])).
% 2.63/1.37  tff(c_185, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_182])).
% 2.63/1.37  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_185])).
% 2.63/1.37  tff(c_190, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_129])).
% 2.63/1.37  tff(c_52, plain, (![A_64]: (v1_funct_1(A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.63/1.37  tff(c_201, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_190, c_52])).
% 2.63/1.37  tff(c_99, plain, (![A_81]: (k1_relat_1(A_81)=k1_xboole_0 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_91, c_4])).
% 2.63/1.37  tff(c_200, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_99])).
% 2.63/1.37  tff(c_425, plain, (![A_160, B_161]: (r2_hidden('#skF_4'(A_160, B_161), k1_relat_1(B_161)) | v5_funct_1(B_161, A_160) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.63/1.37  tff(c_428, plain, (![A_160]: (r2_hidden('#skF_4'(A_160, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_160) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_200, c_425])).
% 2.63/1.37  tff(c_433, plain, (![A_160]: (r2_hidden('#skF_4'(A_160, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_160) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_201, c_428])).
% 2.63/1.37  tff(c_436, plain, (![A_162]: (v5_funct_1(k1_xboole_0, A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(negUnitSimplification, [status(thm)], [c_249, c_433])).
% 2.63/1.37  tff(c_60, plain, (~v5_funct_1(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.63/1.37  tff(c_439, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_436, c_60])).
% 2.63/1.37  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_439])).
% 2.63/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  Inference rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Ref     : 1
% 2.63/1.37  #Sup     : 78
% 2.63/1.37  #Fact    : 0
% 2.63/1.37  #Define  : 0
% 2.63/1.37  #Split   : 1
% 2.63/1.37  #Chain   : 0
% 2.63/1.37  #Close   : 0
% 2.63/1.37  
% 2.63/1.37  Ordering : KBO
% 2.63/1.37  
% 2.63/1.37  Simplification rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Subsume      : 13
% 2.63/1.37  #Demod        : 26
% 2.63/1.37  #Tautology    : 49
% 2.63/1.37  #SimpNegUnit  : 5
% 2.63/1.37  #BackRed      : 0
% 2.63/1.37  
% 2.63/1.37  #Partial instantiations: 0
% 2.63/1.37  #Strategies tried      : 1
% 2.63/1.37  
% 2.63/1.37  Timing (in seconds)
% 2.63/1.37  ----------------------
% 2.63/1.38  Preprocessing        : 0.34
% 2.63/1.38  Parsing              : 0.18
% 2.63/1.38  CNF conversion       : 0.02
% 2.63/1.38  Main loop            : 0.23
% 2.63/1.38  Inferencing          : 0.09
% 2.63/1.38  Reduction            : 0.07
% 2.63/1.38  Demodulation         : 0.05
% 2.63/1.38  BG Simplification    : 0.02
% 2.63/1.38  Subsumption          : 0.04
% 2.63/1.38  Abstraction          : 0.01
% 2.63/1.38  MUC search           : 0.00
% 2.63/1.38  Cooper               : 0.00
% 2.63/1.38  Total                : 0.60
% 2.63/1.38  Index Insertion      : 0.00
% 2.63/1.38  Index Deletion       : 0.00
% 2.63/1.38  Index Matching       : 0.00
% 2.63/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
