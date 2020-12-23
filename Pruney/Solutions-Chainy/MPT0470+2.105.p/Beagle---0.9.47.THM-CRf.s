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
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 126 expanded)
%              Number of leaves         :   38 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 204 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_74,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [A_71,C_72,B_73] :
      ( ~ r2_hidden(A_71,C_72)
      | ~ r1_xboole_0(k2_tarski(A_71,B_73),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_76] : ~ r2_hidden(A_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_34,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_418,plain,(
    ! [A_110,B_111] :
      ( k1_relat_1(k5_relat_1(A_110,B_111)) = k1_relat_1(A_110)
      | ~ r1_tarski(k2_relat_1(A_110),k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_427,plain,(
    ! [B_111] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_111)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_418])).

tff(c_434,plain,(
    ! [B_112] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_112)) = k1_xboole_0
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_12,c_46,c_427])).

tff(c_36,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k1_relat_1(A_45))
      | ~ v1_relat_1(A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_446,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_112))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_36])).

tff(c_459,plain,(
    ! [B_113] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_113))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_113))
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_446])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_491,plain,(
    ! [B_115] :
      ( k5_relat_1(k1_xboole_0,B_115) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_459,c_4])).

tff(c_498,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_491])).

tff(c_504,plain,(
    ! [B_116] :
      ( k5_relat_1(k1_xboole_0,B_116) = k1_xboole_0
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_498])).

tff(c_513,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_504])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_513])).

tff(c_521,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_586,plain,(
    ! [A_130,C_131,B_132] :
      ( ~ r2_hidden(A_130,C_131)
      | ~ r1_xboole_0(k2_tarski(A_130,B_132),C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_598,plain,(
    ! [A_135] : ~ r2_hidden(A_135,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_586])).

tff(c_603,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_598])).

tff(c_69,plain,(
    ! [A_57,B_58] :
      ( v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | ~ v1_xboole_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_528,plain,(
    ! [A_118,B_119] :
      ( k2_zfmisc_1(A_118,B_119) = k1_xboole_0
      | ~ v1_xboole_0(B_119) ) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_534,plain,(
    ! [A_118] : k2_zfmisc_1(A_118,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_528])).

tff(c_662,plain,(
    ! [A_147,B_148] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_147,B_148)),k2_relat_1(B_148))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_670,plain,(
    ! [A_147] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_147,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_662])).

tff(c_676,plain,(
    ! [A_149] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_149,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_670])).

tff(c_563,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(B_127,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_572,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_563])).

tff(c_686,plain,(
    ! [A_150] :
      ( k2_relat_1(k5_relat_1(A_150,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_676,c_572])).

tff(c_38,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46)))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_701,plain,(
    ! [A_150] :
      ( r1_tarski(k5_relat_1(A_150,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_150,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_150,k1_xboole_0))
      | ~ v1_relat_1(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_38])).

tff(c_720,plain,(
    ! [A_156] :
      ( r1_tarski(k5_relat_1(A_156,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_156,k1_xboole_0))
      | ~ v1_relat_1(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_701])).

tff(c_730,plain,(
    ! [A_157] :
      ( k5_relat_1(A_157,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_157,k1_xboole_0))
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_720,c_572])).

tff(c_734,plain,(
    ! [A_43] :
      ( k5_relat_1(A_43,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_34,c_730])).

tff(c_738,plain,(
    ! [A_158] :
      ( k5_relat_1(A_158,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_734])).

tff(c_747,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_738])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:03:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.81/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.41  
% 2.81/1.43  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.81/1.43  tff(f_67, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.81/1.43  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.81/1.43  tff(f_57, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.81/1.43  tff(f_73, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.81/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.81/1.43  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.43  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.81/1.43  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.81/1.43  tff(f_81, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.81/1.43  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.81/1.43  tff(f_52, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.81/1.43  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.81/1.43  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.43  tff(f_85, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.81/1.43  tff(c_48, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.43  tff(c_74, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.81/1.43  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.43  tff(c_32, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.43  tff(c_14, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.43  tff(c_112, plain, (![A_71, C_72, B_73]: (~r2_hidden(A_71, C_72) | ~r1_xboole_0(k2_tarski(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.43  tff(c_128, plain, (![A_76]: (~r2_hidden(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_112])).
% 2.81/1.43  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_128])).
% 2.81/1.43  tff(c_34, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.81/1.43  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.43  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.81/1.43  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.81/1.43  tff(c_418, plain, (![A_110, B_111]: (k1_relat_1(k5_relat_1(A_110, B_111))=k1_relat_1(A_110) | ~r1_tarski(k2_relat_1(A_110), k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.81/1.43  tff(c_427, plain, (![B_111]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_111))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_418])).
% 2.81/1.43  tff(c_434, plain, (![B_112]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_112))=k1_xboole_0 | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_12, c_46, c_427])).
% 2.81/1.43  tff(c_36, plain, (![A_45]: (~v1_xboole_0(k1_relat_1(A_45)) | ~v1_relat_1(A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.43  tff(c_446, plain, (![B_112]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_112)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_112)) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_434, c_36])).
% 2.81/1.43  tff(c_459, plain, (![B_113]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_113)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_113)) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_446])).
% 2.81/1.43  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.81/1.43  tff(c_491, plain, (![B_115]: (k5_relat_1(k1_xboole_0, B_115)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_115)) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_459, c_4])).
% 2.81/1.43  tff(c_498, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_491])).
% 2.81/1.43  tff(c_504, plain, (![B_116]: (k5_relat_1(k1_xboole_0, B_116)=k1_xboole_0 | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_498])).
% 2.81/1.43  tff(c_513, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_504])).
% 2.81/1.43  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_513])).
% 2.81/1.43  tff(c_521, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.81/1.43  tff(c_586, plain, (![A_130, C_131, B_132]: (~r2_hidden(A_130, C_131) | ~r1_xboole_0(k2_tarski(A_130, B_132), C_131))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.43  tff(c_598, plain, (![A_135]: (~r2_hidden(A_135, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_586])).
% 2.81/1.43  tff(c_603, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_598])).
% 2.81/1.43  tff(c_69, plain, (![A_57, B_58]: (v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | ~v1_xboole_0(B_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.43  tff(c_528, plain, (![A_118, B_119]: (k2_zfmisc_1(A_118, B_119)=k1_xboole_0 | ~v1_xboole_0(B_119))), inference(resolution, [status(thm)], [c_69, c_4])).
% 2.81/1.43  tff(c_534, plain, (![A_118]: (k2_zfmisc_1(A_118, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_528])).
% 2.81/1.43  tff(c_662, plain, (![A_147, B_148]: (r1_tarski(k2_relat_1(k5_relat_1(A_147, B_148)), k2_relat_1(B_148)) | ~v1_relat_1(B_148) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.43  tff(c_670, plain, (![A_147]: (r1_tarski(k2_relat_1(k5_relat_1(A_147, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_44, c_662])).
% 2.81/1.43  tff(c_676, plain, (![A_149]: (r1_tarski(k2_relat_1(k5_relat_1(A_149, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_670])).
% 2.81/1.43  tff(c_563, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(B_127, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.81/1.43  tff(c_572, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_563])).
% 2.81/1.43  tff(c_686, plain, (![A_150]: (k2_relat_1(k5_relat_1(A_150, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_676, c_572])).
% 2.81/1.43  tff(c_38, plain, (![A_46]: (r1_tarski(A_46, k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46))) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.43  tff(c_701, plain, (![A_150]: (r1_tarski(k5_relat_1(A_150, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_150, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_150, k1_xboole_0)) | ~v1_relat_1(A_150))), inference(superposition, [status(thm), theory('equality')], [c_686, c_38])).
% 2.81/1.43  tff(c_720, plain, (![A_156]: (r1_tarski(k5_relat_1(A_156, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_156, k1_xboole_0)) | ~v1_relat_1(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_701])).
% 2.81/1.43  tff(c_730, plain, (![A_157]: (k5_relat_1(A_157, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_157, k1_xboole_0)) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_720, c_572])).
% 2.81/1.43  tff(c_734, plain, (![A_43]: (k5_relat_1(A_43, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_34, c_730])).
% 2.81/1.43  tff(c_738, plain, (![A_158]: (k5_relat_1(A_158, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_734])).
% 2.81/1.43  tff(c_747, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_738])).
% 2.81/1.43  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_521, c_747])).
% 2.81/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  Inference rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Ref     : 1
% 2.81/1.43  #Sup     : 150
% 2.81/1.43  #Fact    : 0
% 2.81/1.43  #Define  : 0
% 2.81/1.43  #Split   : 1
% 2.81/1.43  #Chain   : 0
% 2.81/1.43  #Close   : 0
% 2.81/1.43  
% 2.81/1.43  Ordering : KBO
% 2.81/1.43  
% 2.81/1.43  Simplification rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Subsume      : 6
% 2.81/1.43  #Demod        : 140
% 2.81/1.43  #Tautology    : 100
% 2.81/1.43  #SimpNegUnit  : 2
% 2.81/1.43  #BackRed      : 0
% 2.81/1.43  
% 2.81/1.43  #Partial instantiations: 0
% 2.81/1.43  #Strategies tried      : 1
% 2.81/1.43  
% 2.81/1.43  Timing (in seconds)
% 2.81/1.43  ----------------------
% 2.81/1.43  Preprocessing        : 0.33
% 2.81/1.43  Parsing              : 0.17
% 2.81/1.43  CNF conversion       : 0.02
% 2.81/1.43  Main loop            : 0.32
% 2.81/1.43  Inferencing          : 0.12
% 2.81/1.43  Reduction            : 0.09
% 2.81/1.43  Demodulation         : 0.07
% 2.81/1.43  BG Simplification    : 0.02
% 2.81/1.43  Subsumption          : 0.06
% 2.81/1.43  Abstraction          : 0.02
% 2.81/1.43  MUC search           : 0.00
% 2.81/1.43  Cooper               : 0.00
% 2.81/1.43  Total                : 0.68
% 2.81/1.43  Index Insertion      : 0.00
% 2.81/1.43  Index Deletion       : 0.00
% 2.81/1.43  Index Matching       : 0.00
% 2.81/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
