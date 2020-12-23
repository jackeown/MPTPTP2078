%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 22.58s
% Output     : CNFRefutation 22.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 167 expanded)
%              Number of leaves         :   38 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 281 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_143,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_640,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_tarski(k4_xboole_0(A_187,B_188),C_189)
      | ~ r1_tarski(A_187,k2_xboole_0(B_188,C_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_975,plain,(
    ! [A_232,B_233] :
      ( k4_xboole_0(A_232,B_233) = k1_xboole_0
      | ~ r1_tarski(A_232,k2_xboole_0(B_233,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_640,c_32])).

tff(c_1063,plain,(
    ! [A_237] : k4_xboole_0(A_237,A_237) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_975])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1080,plain,(
    ! [A_237] :
      ( k2_xboole_0(A_237,k1_xboole_0) = A_237
      | ~ r1_tarski(A_237,A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_36])).

tff(c_1113,plain,(
    ! [A_237] : k2_xboole_0(A_237,k1_xboole_0) = A_237 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1080])).

tff(c_24,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1029,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_975])).

tff(c_1033,plain,(
    ! [A_234,B_235,C_236] : r1_tarski(k2_xboole_0(k3_xboole_0(A_234,B_235),k3_xboole_0(A_234,C_236)),k2_xboole_0(B_235,C_236)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104213,plain,(
    ! [A_15374,A_15375,B_15376] :
      ( r1_tarski(k2_xboole_0(k3_xboole_0(A_15374,A_15375),k3_xboole_0(A_15374,k4_xboole_0(B_15376,A_15375))),B_15376)
      | ~ r1_tarski(A_15375,B_15376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1033])).

tff(c_104399,plain,(
    ! [A_15374,A_30] :
      ( r1_tarski(k2_xboole_0(k3_xboole_0(A_15374,A_30),k3_xboole_0(A_15374,k1_xboole_0)),A_30)
      | ~ r1_tarski(A_30,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_104213])).

tff(c_108174,plain,(
    ! [A_15529,A_15530] : r1_tarski(k2_xboole_0(k3_xboole_0(A_15529,A_15530),k3_xboole_0(A_15529,k1_xboole_0)),A_15530) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104399])).

tff(c_108309,plain,(
    ! [A_15529] : k2_xboole_0(k3_xboole_0(A_15529,k1_xboole_0),k3_xboole_0(A_15529,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108174,c_32])).

tff(c_108954,plain,(
    ! [A_15537] : k2_xboole_0(k3_xboole_0(A_15537,k1_xboole_0),k3_xboole_0(A_15537,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108174,c_32])).

tff(c_403,plain,(
    ! [B_153,A_154] :
      ( B_153 = A_154
      | ~ r1_tarski(B_153,A_154)
      | ~ r1_tarski(A_154,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_427,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(k2_xboole_0(A_30,B_31),A_30) ) ),
    inference(resolution,[status(thm)],[c_38,c_403])).

tff(c_109019,plain,(
    ! [A_15537] :
      ( k2_xboole_0(k3_xboole_0(A_15537,k1_xboole_0),k3_xboole_0(A_15537,k1_xboole_0)) = k3_xboole_0(A_15537,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k3_xboole_0(A_15537,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108954,c_427])).

tff(c_109119,plain,(
    ! [A_15537] : k3_xboole_0(A_15537,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_108309,c_109019])).

tff(c_104428,plain,(
    ! [A_15374,A_30] : r1_tarski(k2_xboole_0(k3_xboole_0(A_15374,A_30),k3_xboole_0(A_15374,k1_xboole_0)),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104399])).

tff(c_109140,plain,(
    ! [A_15374,A_30] : r1_tarski(k2_xboole_0(k3_xboole_0(A_15374,A_30),k1_xboole_0),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109119,c_104428])).

tff(c_109148,plain,(
    ! [A_15374,A_30] : r1_tarski(k3_xboole_0(A_15374,A_30),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_109140])).

tff(c_90,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_82,plain,(
    ! [A_67,B_68] :
      ( v1_relat_1(k3_xboole_0(A_67,B_68))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_88,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_92,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6333,plain,(
    ! [C_405,A_406,B_407] :
      ( r1_tarski(k5_relat_1(C_405,A_406),k5_relat_1(C_405,B_407))
      | ~ r1_tarski(A_406,B_407)
      | ~ v1_relat_1(C_405)
      | ~ v1_relat_1(B_407)
      | ~ v1_relat_1(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3507,plain,(
    ! [C_320,A_321,B_322] :
      ( r1_tarski(k5_relat_1(C_320,A_321),k5_relat_1(C_320,B_322))
      | ~ r1_tarski(A_321,B_322)
      | ~ v1_relat_1(C_320)
      | ~ v1_relat_1(B_322)
      | ~ v1_relat_1(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1446,plain,(
    ! [A_248,B_249,C_250] :
      ( r1_tarski(A_248,k3_xboole_0(B_249,C_250))
      | ~ r1_tarski(A_248,C_250)
      | ~ r1_tarski(A_248,B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ~ r1_tarski(k5_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')),k3_xboole_0(k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1484,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')),k5_relat_1('#skF_6','#skF_8'))
    | ~ r1_tarski(k5_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')),k5_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1446,c_86])).

tff(c_1964,plain,(
    ~ r1_tarski(k5_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')),k5_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_3510,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3507,c_1964])).

tff(c_3521,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_92,c_20,c_3510])).

tff(c_3527,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_3521])).

tff(c_3531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3527])).

tff(c_3532,plain,(
    ~ r1_tarski(k5_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')),k5_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_6339,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),'#skF_8')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_6333,c_3532])).

tff(c_6351,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),'#skF_8')
    | ~ v1_relat_1(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92,c_6339])).

tff(c_6397,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6351])).

tff(c_6400,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_6397])).

tff(c_6404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6400])).

tff(c_6405,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_6351])).

tff(c_109377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109148,c_6405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:14:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.58/12.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.58/12.49  
% 22.58/12.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.58/12.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 22.58/12.49  
% 22.58/12.49  %Foreground sorts:
% 22.58/12.49  
% 22.58/12.49  
% 22.58/12.49  %Background operators:
% 22.58/12.49  
% 22.58/12.49  
% 22.58/12.49  %Foreground operators:
% 22.58/12.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.58/12.49  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 22.58/12.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.58/12.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.58/12.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.58/12.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.58/12.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 22.58/12.49  tff('#skF_7', type, '#skF_7': $i).
% 22.58/12.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.58/12.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.58/12.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.58/12.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.58/12.49  tff('#skF_6', type, '#skF_6': $i).
% 22.58/12.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 22.58/12.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.58/12.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.58/12.49  tff('#skF_8', type, '#skF_8': $i).
% 22.58/12.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.58/12.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.58/12.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.58/12.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.58/12.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.58/12.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.58/12.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.58/12.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.58/12.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.58/12.49  
% 22.68/12.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.68/12.50  tff(f_76, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 22.68/12.50  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 22.68/12.50  tff(f_66, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 22.68/12.50  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 22.68/12.50  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.68/12.50  tff(f_56, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 22.68/12.50  tff(f_154, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 22.68/12.50  tff(f_131, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 22.68/12.50  tff(f_143, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 22.68/12.50  tff(f_46, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 22.68/12.50  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 22.68/12.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.68/12.50  tff(c_38, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.68/12.50  tff(c_640, plain, (![A_187, B_188, C_189]: (r1_tarski(k4_xboole_0(A_187, B_188), C_189) | ~r1_tarski(A_187, k2_xboole_0(B_188, C_189)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.68/12.50  tff(c_32, plain, (![A_24]: (k1_xboole_0=A_24 | ~r1_tarski(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.68/12.50  tff(c_975, plain, (![A_232, B_233]: (k4_xboole_0(A_232, B_233)=k1_xboole_0 | ~r1_tarski(A_232, k2_xboole_0(B_233, k1_xboole_0)))), inference(resolution, [status(thm)], [c_640, c_32])).
% 22.68/12.50  tff(c_1063, plain, (![A_237]: (k4_xboole_0(A_237, A_237)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_975])).
% 22.68/12.50  tff(c_36, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.68/12.50  tff(c_1080, plain, (![A_237]: (k2_xboole_0(A_237, k1_xboole_0)=A_237 | ~r1_tarski(A_237, A_237))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_36])).
% 22.68/12.50  tff(c_1113, plain, (![A_237]: (k2_xboole_0(A_237, k1_xboole_0)=A_237)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1080])).
% 22.68/12.50  tff(c_24, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 22.68/12.50  tff(c_1029, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_975])).
% 22.68/12.50  tff(c_1033, plain, (![A_234, B_235, C_236]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_234, B_235), k3_xboole_0(A_234, C_236)), k2_xboole_0(B_235, C_236)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.68/12.50  tff(c_104213, plain, (![A_15374, A_15375, B_15376]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_15374, A_15375), k3_xboole_0(A_15374, k4_xboole_0(B_15376, A_15375))), B_15376) | ~r1_tarski(A_15375, B_15376))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1033])).
% 22.68/12.50  tff(c_104399, plain, (![A_15374, A_30]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_15374, A_30), k3_xboole_0(A_15374, k1_xboole_0)), A_30) | ~r1_tarski(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_104213])).
% 22.68/12.50  tff(c_108174, plain, (![A_15529, A_15530]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_15529, A_15530), k3_xboole_0(A_15529, k1_xboole_0)), A_15530))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104399])).
% 22.68/12.50  tff(c_108309, plain, (![A_15529]: (k2_xboole_0(k3_xboole_0(A_15529, k1_xboole_0), k3_xboole_0(A_15529, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_108174, c_32])).
% 22.68/12.50  tff(c_108954, plain, (![A_15537]: (k2_xboole_0(k3_xboole_0(A_15537, k1_xboole_0), k3_xboole_0(A_15537, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_108174, c_32])).
% 22.68/12.50  tff(c_403, plain, (![B_153, A_154]: (B_153=A_154 | ~r1_tarski(B_153, A_154) | ~r1_tarski(A_154, B_153))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.68/12.50  tff(c_427, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(k2_xboole_0(A_30, B_31), A_30))), inference(resolution, [status(thm)], [c_38, c_403])).
% 22.68/12.50  tff(c_109019, plain, (![A_15537]: (k2_xboole_0(k3_xboole_0(A_15537, k1_xboole_0), k3_xboole_0(A_15537, k1_xboole_0))=k3_xboole_0(A_15537, k1_xboole_0) | ~r1_tarski(k1_xboole_0, k3_xboole_0(A_15537, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_108954, c_427])).
% 22.68/12.50  tff(c_109119, plain, (![A_15537]: (k3_xboole_0(A_15537, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_108309, c_109019])).
% 22.68/12.50  tff(c_104428, plain, (![A_15374, A_30]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_15374, A_30), k3_xboole_0(A_15374, k1_xboole_0)), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104399])).
% 22.68/12.50  tff(c_109140, plain, (![A_15374, A_30]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_15374, A_30), k1_xboole_0), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_109119, c_104428])).
% 22.68/12.50  tff(c_109148, plain, (![A_15374, A_30]: (r1_tarski(k3_xboole_0(A_15374, A_30), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_1113, c_109140])).
% 22.68/12.50  tff(c_90, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.68/12.50  tff(c_82, plain, (![A_67, B_68]: (v1_relat_1(k3_xboole_0(A_67, B_68)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_131])).
% 22.68/12.50  tff(c_88, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.68/12.50  tff(c_92, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.68/12.50  tff(c_6333, plain, (![C_405, A_406, B_407]: (r1_tarski(k5_relat_1(C_405, A_406), k5_relat_1(C_405, B_407)) | ~r1_tarski(A_406, B_407) | ~v1_relat_1(C_405) | ~v1_relat_1(B_407) | ~v1_relat_1(A_406))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.68/12.50  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.68/12.50  tff(c_3507, plain, (![C_320, A_321, B_322]: (r1_tarski(k5_relat_1(C_320, A_321), k5_relat_1(C_320, B_322)) | ~r1_tarski(A_321, B_322) | ~v1_relat_1(C_320) | ~v1_relat_1(B_322) | ~v1_relat_1(A_321))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.68/12.50  tff(c_1446, plain, (![A_248, B_249, C_250]: (r1_tarski(A_248, k3_xboole_0(B_249, C_250)) | ~r1_tarski(A_248, C_250) | ~r1_tarski(A_248, B_249))), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.68/12.50  tff(c_86, plain, (~r1_tarski(k5_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')), k3_xboole_0(k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.68/12.50  tff(c_1484, plain, (~r1_tarski(k5_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')), k5_relat_1('#skF_6', '#skF_8')) | ~r1_tarski(k5_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')), k5_relat_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1446, c_86])).
% 22.68/12.50  tff(c_1964, plain, (~r1_tarski(k5_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')), k5_relat_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1484])).
% 22.68/12.50  tff(c_3510, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), '#skF_7') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7') | ~v1_relat_1(k3_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_3507, c_1964])).
% 22.68/12.50  tff(c_3521, plain, (~v1_relat_1(k3_xboole_0('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_92, c_20, c_3510])).
% 22.68/12.50  tff(c_3527, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_82, c_3521])).
% 22.68/12.50  tff(c_3531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_3527])).
% 22.68/12.50  tff(c_3532, plain, (~r1_tarski(k5_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')), k5_relat_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1484])).
% 22.68/12.50  tff(c_6339, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), '#skF_8') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_8') | ~v1_relat_1(k3_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_6333, c_3532])).
% 22.68/12.50  tff(c_6351, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), '#skF_8') | ~v1_relat_1(k3_xboole_0('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_92, c_6339])).
% 22.68/12.50  tff(c_6397, plain, (~v1_relat_1(k3_xboole_0('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_6351])).
% 22.68/12.50  tff(c_6400, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_82, c_6397])).
% 22.68/12.50  tff(c_6404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_6400])).
% 22.68/12.50  tff(c_6405, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_6351])).
% 22.68/12.50  tff(c_109377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109148, c_6405])).
% 22.68/12.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.68/12.50  
% 22.68/12.50  Inference rules
% 22.68/12.50  ----------------------
% 22.68/12.50  #Ref     : 0
% 22.68/12.50  #Sup     : 20637
% 22.68/12.50  #Fact    : 2
% 22.68/12.50  #Define  : 0
% 22.68/12.50  #Split   : 8
% 22.68/12.50  #Chain   : 0
% 22.68/12.50  #Close   : 0
% 22.68/12.50  
% 22.68/12.50  Ordering : KBO
% 22.68/12.50  
% 22.68/12.50  Simplification rules
% 22.68/12.50  ----------------------
% 22.68/12.50  #Subsume      : 2176
% 22.68/12.50  #Demod        : 4487
% 22.68/12.50  #Tautology    : 2434
% 22.68/12.50  #SimpNegUnit  : 18
% 22.68/12.50  #BackRed      : 45
% 22.68/12.50  
% 22.68/12.50  #Partial instantiations: 10152
% 22.68/12.50  #Strategies tried      : 1
% 22.68/12.50  
% 22.68/12.50  Timing (in seconds)
% 22.68/12.50  ----------------------
% 22.68/12.51  Preprocessing        : 0.33
% 22.68/12.51  Parsing              : 0.18
% 22.68/12.51  CNF conversion       : 0.03
% 22.68/12.51  Main loop            : 11.42
% 22.68/12.51  Inferencing          : 1.86
% 22.68/12.51  Reduction            : 5.02
% 22.68/12.51  Demodulation         : 4.26
% 22.68/12.51  BG Simplification    : 0.35
% 22.68/12.51  Subsumption          : 3.30
% 22.68/12.51  Abstraction          : 0.39
% 22.68/12.51  MUC search           : 0.00
% 22.68/12.51  Cooper               : 0.00
% 22.68/12.51  Total                : 11.79
% 22.68/12.51  Index Insertion      : 0.00
% 22.68/12.51  Index Deletion       : 0.00
% 22.68/12.51  Index Matching       : 0.00
% 22.68/12.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
