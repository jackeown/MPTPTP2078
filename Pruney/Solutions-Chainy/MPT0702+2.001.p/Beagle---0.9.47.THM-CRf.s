%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:02 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 170 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 386 expanded)
%              Number of equality atoms :   43 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(A_49,B_50)
      | k4_xboole_0(A_49,B_50) != A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_329,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | k4_xboole_0(A_61,B_60) != A_61 ) ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5661,plain,(
    ! [B_198,A_199] :
      ( k4_xboole_0(B_198,A_199) = B_198
      | k4_xboole_0(A_199,B_198) != A_199 ) ),
    inference(resolution,[status(thm)],[c_329,c_22])).

tff(c_5689,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k4_xboole_0(A_13,B_14)
      | k3_xboole_0(A_13,B_14) != A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5661])).

tff(c_6525,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(A_210,B_211) = k1_xboole_0
      | k3_xboole_0(A_210,B_211) != A_210 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5689])).

tff(c_231,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_244,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_38])).

tff(c_6785,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6525,c_244])).

tff(c_337,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_463,plain,(
    ! [A_68,B_69] : r1_tarski(k3_xboole_0(A_68,B_69),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_16])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_486,plain,(
    ! [A_68,B_69] : k4_xboole_0(k3_xboole_0(A_68,B_69),A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_463,c_12])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k10_relat_1(B_27,k9_relat_1(B_27,A_26)))
      | ~ r1_tarski(A_26,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_802,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k10_relat_1(B_85,k9_relat_1(B_85,A_86)),A_86)
      | ~ v2_funct_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5707,plain,(
    ! [B_200,A_201] :
      ( k10_relat_1(B_200,k9_relat_1(B_200,A_201)) = A_201
      | ~ r1_tarski(A_201,k10_relat_1(B_200,k9_relat_1(B_200,A_201)))
      | ~ v2_funct_1(B_200)
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_802,c_4])).

tff(c_21542,plain,(
    ! [B_369,A_370] :
      ( k10_relat_1(B_369,k9_relat_1(B_369,A_370)) = A_370
      | ~ v2_funct_1(B_369)
      | ~ v1_funct_1(B_369)
      | ~ r1_tarski(A_370,k1_relat_1(B_369))
      | ~ v1_relat_1(B_369) ) ),
    inference(resolution,[status(thm)],[c_34,c_5707])).

tff(c_21626,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_21542])).

tff(c_21671,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_21626])).

tff(c_44,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_137,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_124])).

tff(c_5693,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = A_10
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_5661])).

tff(c_7157,plain,(
    ! [A_218,B_219] :
      ( k3_xboole_0(A_218,B_219) = A_218
      | k4_xboole_0(A_218,B_219) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5693])).

tff(c_7237,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_7157])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( k3_xboole_0(k9_relat_1(C_25,A_23),k9_relat_1(C_25,B_24)) = k9_relat_1(C_25,k3_xboole_0(A_23,B_24))
      | ~ v2_funct_1(C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7998,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7237,c_32])).

tff(c_8035,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_7998])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28202,plain,(
    ! [B_432,A_433] :
      ( k10_relat_1(B_432,k9_relat_1(B_432,A_433)) = A_433
      | ~ v2_funct_1(B_432)
      | ~ v1_funct_1(B_432)
      | ~ v1_relat_1(B_432)
      | k4_xboole_0(A_433,k10_relat_1(B_432,k9_relat_1(B_432,A_433))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_5707])).

tff(c_28243,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) = k3_xboole_0('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8035,c_28202])).

tff(c_28285,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_21671,c_48,c_46,c_40,c_21671,c_8035,c_28243])).

tff(c_28287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6785,c_28285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.12/4.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.50  
% 11.12/4.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.51  %$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.12/4.51  
% 11.12/4.51  %Foreground sorts:
% 11.12/4.51  
% 11.12/4.51  
% 11.12/4.51  %Background operators:
% 11.12/4.51  
% 11.12/4.51  
% 11.12/4.51  %Foreground operators:
% 11.12/4.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.12/4.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.12/4.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.12/4.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.12/4.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.12/4.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.12/4.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.12/4.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.12/4.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.12/4.51  tff('#skF_2', type, '#skF_2': $i).
% 11.12/4.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.12/4.51  tff('#skF_3', type, '#skF_3': $i).
% 11.12/4.51  tff('#skF_1', type, '#skF_1': $i).
% 11.12/4.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.12/4.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.12/4.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.12/4.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.12/4.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.12/4.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.12/4.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.12/4.51  
% 11.12/4.52  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.12/4.52  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.12/4.52  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.12/4.52  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.12/4.52  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.12/4.52  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 11.12/4.52  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 11.12/4.52  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 11.12/4.52  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.12/4.52  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 11.12/4.52  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.12/4.52  tff(c_124, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.12/4.52  tff(c_138, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_124])).
% 11.12/4.52  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.12/4.52  tff(c_223, plain, (![A_49, B_50]: (r1_xboole_0(A_49, B_50) | k4_xboole_0(A_49, B_50)!=A_49)), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.12/4.52  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.12/4.52  tff(c_329, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | k4_xboole_0(A_61, B_60)!=A_61)), inference(resolution, [status(thm)], [c_223, c_2])).
% 11.12/4.52  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.12/4.52  tff(c_5661, plain, (![B_198, A_199]: (k4_xboole_0(B_198, A_199)=B_198 | k4_xboole_0(A_199, B_198)!=A_199)), inference(resolution, [status(thm)], [c_329, c_22])).
% 11.12/4.52  tff(c_5689, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k4_xboole_0(A_13, B_14) | k3_xboole_0(A_13, B_14)!=A_13)), inference(superposition, [status(thm), theory('equality')], [c_20, c_5661])).
% 11.12/4.52  tff(c_6525, plain, (![A_210, B_211]: (k4_xboole_0(A_210, B_211)=k1_xboole_0 | k3_xboole_0(A_210, B_211)!=A_210)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5689])).
% 11.12/4.52  tff(c_231, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.12/4.52  tff(c_38, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_244, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_231, c_38])).
% 11.12/4.52  tff(c_6785, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6525, c_244])).
% 11.12/4.52  tff(c_337, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.12/4.52  tff(c_463, plain, (![A_68, B_69]: (r1_tarski(k3_xboole_0(A_68, B_69), A_68))), inference(superposition, [status(thm), theory('equality')], [c_337, c_16])).
% 11.12/4.52  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.12/4.52  tff(c_486, plain, (![A_68, B_69]: (k4_xboole_0(k3_xboole_0(A_68, B_69), A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_463, c_12])).
% 11.12/4.52  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_42, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_34, plain, (![A_26, B_27]: (r1_tarski(A_26, k10_relat_1(B_27, k9_relat_1(B_27, A_26))) | ~r1_tarski(A_26, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.12/4.52  tff(c_802, plain, (![B_85, A_86]: (r1_tarski(k10_relat_1(B_85, k9_relat_1(B_85, A_86)), A_86) | ~v2_funct_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.12/4.52  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.12/4.52  tff(c_5707, plain, (![B_200, A_201]: (k10_relat_1(B_200, k9_relat_1(B_200, A_201))=A_201 | ~r1_tarski(A_201, k10_relat_1(B_200, k9_relat_1(B_200, A_201))) | ~v2_funct_1(B_200) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_802, c_4])).
% 11.12/4.52  tff(c_21542, plain, (![B_369, A_370]: (k10_relat_1(B_369, k9_relat_1(B_369, A_370))=A_370 | ~v2_funct_1(B_369) | ~v1_funct_1(B_369) | ~r1_tarski(A_370, k1_relat_1(B_369)) | ~v1_relat_1(B_369))), inference(resolution, [status(thm)], [c_34, c_5707])).
% 11.12/4.52  tff(c_21626, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_21542])).
% 11.12/4.52  tff(c_21671, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_21626])).
% 11.12/4.52  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.12/4.52  tff(c_137, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_124])).
% 11.12/4.52  tff(c_5693, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=A_10 | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_5661])).
% 11.12/4.52  tff(c_7157, plain, (![A_218, B_219]: (k3_xboole_0(A_218, B_219)=A_218 | k4_xboole_0(A_218, B_219)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5693])).
% 11.12/4.52  tff(c_7237, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_137, c_7157])).
% 11.12/4.52  tff(c_32, plain, (![C_25, A_23, B_24]: (k3_xboole_0(k9_relat_1(C_25, A_23), k9_relat_1(C_25, B_24))=k9_relat_1(C_25, k3_xboole_0(A_23, B_24)) | ~v2_funct_1(C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.12/4.52  tff(c_7998, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7237, c_32])).
% 11.12/4.52  tff(c_8035, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_7998])).
% 11.12/4.52  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.12/4.52  tff(c_28202, plain, (![B_432, A_433]: (k10_relat_1(B_432, k9_relat_1(B_432, A_433))=A_433 | ~v2_funct_1(B_432) | ~v1_funct_1(B_432) | ~v1_relat_1(B_432) | k4_xboole_0(A_433, k10_relat_1(B_432, k9_relat_1(B_432, A_433)))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_5707])).
% 11.12/4.52  tff(c_28243, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))=k3_xboole_0('#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8035, c_28202])).
% 11.12/4.52  tff(c_28285, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_21671, c_48, c_46, c_40, c_21671, c_8035, c_28243])).
% 11.12/4.52  tff(c_28287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6785, c_28285])).
% 11.12/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.52  
% 11.12/4.52  Inference rules
% 11.12/4.52  ----------------------
% 11.12/4.52  #Ref     : 4
% 11.12/4.52  #Sup     : 7280
% 11.12/4.52  #Fact    : 0
% 11.12/4.52  #Define  : 0
% 11.12/4.52  #Split   : 7
% 11.12/4.52  #Chain   : 0
% 11.12/4.52  #Close   : 0
% 11.12/4.52  
% 11.12/4.52  Ordering : KBO
% 11.12/4.52  
% 11.12/4.52  Simplification rules
% 11.12/4.52  ----------------------
% 11.12/4.52  #Subsume      : 2283
% 11.12/4.52  #Demod        : 3794
% 11.12/4.52  #Tautology    : 3229
% 11.12/4.52  #SimpNegUnit  : 64
% 11.12/4.52  #BackRed      : 16
% 11.12/4.52  
% 11.12/4.52  #Partial instantiations: 0
% 11.12/4.52  #Strategies tried      : 1
% 11.12/4.52  
% 11.12/4.52  Timing (in seconds)
% 11.12/4.52  ----------------------
% 11.12/4.52  Preprocessing        : 0.33
% 11.12/4.52  Parsing              : 0.17
% 11.12/4.52  CNF conversion       : 0.02
% 11.12/4.52  Main loop            : 3.43
% 11.12/4.52  Inferencing          : 0.64
% 11.12/4.52  Reduction            : 1.69
% 11.12/4.52  Demodulation         : 1.40
% 11.12/4.52  BG Simplification    : 0.08
% 11.12/4.52  Subsumption          : 0.83
% 11.12/4.52  Abstraction          : 0.12
% 11.12/4.52  MUC search           : 0.00
% 11.12/4.52  Cooper               : 0.00
% 11.12/4.52  Total                : 3.79
% 11.12/4.52  Index Insertion      : 0.00
% 11.12/4.52  Index Deletion       : 0.00
% 11.12/4.52  Index Matching       : 0.00
% 11.12/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
