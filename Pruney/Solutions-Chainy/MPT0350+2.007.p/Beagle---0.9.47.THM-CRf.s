%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 139 expanded)
%              Number of leaves         :   42 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 203 expanded)
%              Number of equality atoms :   40 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_48,plain,(
    ! [A_49] : k2_subset_1(A_49) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_61,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    ! [A_54] : ~ v1_xboole_0(k1_zfmisc_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_203,plain,(
    ! [B_82,A_83] :
      ( r2_hidden(B_82,A_83)
      | ~ m1_subset_1(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [C_44,A_40] :
      ( r1_tarski(C_44,A_40)
      | ~ r2_hidden(C_44,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_207,plain,(
    ! [B_82,A_40] :
      ( r1_tarski(B_82,A_40)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_40))
      | v1_xboole_0(k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_203,c_26])).

tff(c_260,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_207])).

tff(c_269,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_260])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_180,plain,(
    ! [B_80,A_81] : k3_tarski(k2_tarski(B_80,A_81)) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_156])).

tff(c_38,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_186,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_38])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_276,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_269,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_357,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_370,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_357])).

tff(c_245,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_313,plain,(
    ! [B_94,A_95] : k5_xboole_0(B_94,k3_xboole_0(A_95,B_94)) = k4_xboole_0(B_94,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_326,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_313])).

tff(c_371,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_326])).

tff(c_386,plain,(
    ! [A_103,B_104] : k2_xboole_0(k5_xboole_0(A_103,B_104),k3_xboole_0(A_103,B_104)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_401,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_386])).

tff(c_428,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_186,c_276,c_186,c_2,c_401])).

tff(c_471,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k3_subset_1(A_105,B_106),k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_210,plain,(
    ! [B_82,A_40] :
      ( r1_tarski(B_82,A_40)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_207])).

tff(c_482,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k3_subset_1(A_105,B_106),A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_471,c_210])).

tff(c_28,plain,(
    ! [C_44,A_40] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_44,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,(
    ! [B_90,A_91] :
      ( m1_subset_1(B_90,A_91)
      | ~ r2_hidden(B_90,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_299,plain,(
    ! [C_44,A_40] :
      ( m1_subset_1(C_44,k1_zfmisc_1(A_40))
      | v1_xboole_0(k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_44,A_40) ) ),
    inference(resolution,[status(thm)],[c_28,c_293])).

tff(c_303,plain,(
    ! [C_44,A_40] :
      ( m1_subset_1(C_44,k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_44,A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_299])).

tff(c_1046,plain,(
    ! [A_148,B_149,C_150] :
      ( k4_subset_1(A_148,B_149,C_150) = k2_xboole_0(B_149,C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1247,plain,(
    ! [A_163,B_164,C_165] :
      ( k4_subset_1(A_163,B_164,C_165) = k2_xboole_0(B_164,C_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_163))
      | ~ r1_tarski(C_165,A_163) ) ),
    inference(resolution,[status(thm)],[c_303,c_1046])).

tff(c_1261,plain,(
    ! [C_166] :
      ( k4_subset_1('#skF_3','#skF_4',C_166) = k2_xboole_0('#skF_4',C_166)
      | ~ r1_tarski(C_166,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_1247])).

tff(c_1274,plain,(
    ! [B_167] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_167)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_167))
      | ~ m1_subset_1(B_167,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_482,c_1261])).

tff(c_1289,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_1274])).

tff(c_1294,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_1289])).

tff(c_1296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_1294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.61  
% 3.69/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.69/1.61  
% 3.69/1.61  %Foreground sorts:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Background operators:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Foreground operators:
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.69/1.61  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.69/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.69/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.69/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.61  
% 3.85/1.63  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.85/1.63  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 3.85/1.63  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.85/1.63  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.85/1.63  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.85/1.63  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.85/1.63  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.85/1.63  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.85/1.63  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.85/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.85/1.63  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.85/1.63  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.85/1.63  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 3.85/1.63  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.85/1.63  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.85/1.63  tff(c_48, plain, (![A_49]: (k2_subset_1(A_49)=A_49)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.63  tff(c_58, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.63  tff(c_61, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58])).
% 3.85/1.63  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.63  tff(c_54, plain, (![A_54]: (~v1_xboole_0(k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.85/1.63  tff(c_203, plain, (![B_82, A_83]: (r2_hidden(B_82, A_83) | ~m1_subset_1(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.85/1.63  tff(c_26, plain, (![C_44, A_40]: (r1_tarski(C_44, A_40) | ~r2_hidden(C_44, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.85/1.63  tff(c_207, plain, (![B_82, A_40]: (r1_tarski(B_82, A_40) | ~m1_subset_1(B_82, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_203, c_26])).
% 3.85/1.63  tff(c_260, plain, (![B_88, A_89]: (r1_tarski(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)))), inference(negUnitSimplification, [status(thm)], [c_54, c_207])).
% 3.85/1.63  tff(c_269, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_260])).
% 3.85/1.63  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.63  tff(c_277, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_269, c_6])).
% 3.85/1.63  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.63  tff(c_156, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.63  tff(c_180, plain, (![B_80, A_81]: (k3_tarski(k2_tarski(B_80, A_81))=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_12, c_156])).
% 3.85/1.63  tff(c_38, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.63  tff(c_186, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_180, c_38])).
% 3.85/1.63  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.85/1.63  tff(c_276, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_269, c_8])).
% 3.85/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.63  tff(c_357, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.85/1.63  tff(c_370, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_357])).
% 3.85/1.63  tff(c_245, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.85/1.63  tff(c_313, plain, (![B_94, A_95]: (k5_xboole_0(B_94, k3_xboole_0(A_95, B_94))=k4_xboole_0(B_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 3.85/1.63  tff(c_326, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_276, c_313])).
% 3.85/1.63  tff(c_371, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_326])).
% 3.85/1.63  tff(c_386, plain, (![A_103, B_104]: (k2_xboole_0(k5_xboole_0(A_103, B_104), k3_xboole_0(A_103, B_104))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.63  tff(c_401, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_371, c_386])).
% 3.85/1.63  tff(c_428, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_186, c_276, c_186, c_2, c_401])).
% 3.85/1.63  tff(c_471, plain, (![A_105, B_106]: (m1_subset_1(k3_subset_1(A_105, B_106), k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.85/1.63  tff(c_210, plain, (![B_82, A_40]: (r1_tarski(B_82, A_40) | ~m1_subset_1(B_82, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_54, c_207])).
% 3.85/1.63  tff(c_482, plain, (![A_105, B_106]: (r1_tarski(k3_subset_1(A_105, B_106), A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_471, c_210])).
% 3.85/1.63  tff(c_28, plain, (![C_44, A_40]: (r2_hidden(C_44, k1_zfmisc_1(A_40)) | ~r1_tarski(C_44, A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.85/1.63  tff(c_293, plain, (![B_90, A_91]: (m1_subset_1(B_90, A_91) | ~r2_hidden(B_90, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.85/1.63  tff(c_299, plain, (![C_44, A_40]: (m1_subset_1(C_44, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)) | ~r1_tarski(C_44, A_40))), inference(resolution, [status(thm)], [c_28, c_293])).
% 3.85/1.63  tff(c_303, plain, (![C_44, A_40]: (m1_subset_1(C_44, k1_zfmisc_1(A_40)) | ~r1_tarski(C_44, A_40))), inference(negUnitSimplification, [status(thm)], [c_54, c_299])).
% 3.85/1.63  tff(c_1046, plain, (![A_148, B_149, C_150]: (k4_subset_1(A_148, B_149, C_150)=k2_xboole_0(B_149, C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.85/1.63  tff(c_1247, plain, (![A_163, B_164, C_165]: (k4_subset_1(A_163, B_164, C_165)=k2_xboole_0(B_164, C_165) | ~m1_subset_1(B_164, k1_zfmisc_1(A_163)) | ~r1_tarski(C_165, A_163))), inference(resolution, [status(thm)], [c_303, c_1046])).
% 3.85/1.63  tff(c_1261, plain, (![C_166]: (k4_subset_1('#skF_3', '#skF_4', C_166)=k2_xboole_0('#skF_4', C_166) | ~r1_tarski(C_166, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_1247])).
% 3.85/1.63  tff(c_1274, plain, (![B_167]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_167))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_167)) | ~m1_subset_1(B_167, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_482, c_1261])).
% 3.85/1.63  tff(c_1289, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1274])).
% 3.85/1.63  tff(c_1294, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_428, c_1289])).
% 3.85/1.63  tff(c_1296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_1294])).
% 3.85/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  
% 3.85/1.63  Inference rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Ref     : 0
% 3.85/1.63  #Sup     : 319
% 3.85/1.63  #Fact    : 0
% 3.85/1.63  #Define  : 0
% 3.85/1.63  #Split   : 0
% 3.85/1.63  #Chain   : 0
% 3.85/1.63  #Close   : 0
% 3.85/1.63  
% 3.85/1.63  Ordering : KBO
% 3.85/1.63  
% 3.85/1.63  Simplification rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Subsume      : 25
% 3.85/1.63  #Demod        : 216
% 3.85/1.63  #Tautology    : 203
% 3.85/1.63  #SimpNegUnit  : 3
% 3.85/1.63  #BackRed      : 6
% 3.85/1.63  
% 3.85/1.63  #Partial instantiations: 0
% 3.85/1.63  #Strategies tried      : 1
% 3.85/1.63  
% 3.85/1.63  Timing (in seconds)
% 3.85/1.63  ----------------------
% 3.85/1.64  Preprocessing        : 0.35
% 3.85/1.64  Parsing              : 0.18
% 3.85/1.64  CNF conversion       : 0.02
% 3.85/1.64  Main loop            : 0.51
% 3.85/1.64  Inferencing          : 0.18
% 3.85/1.64  Reduction            : 0.19
% 3.85/1.64  Demodulation         : 0.15
% 3.85/1.64  BG Simplification    : 0.03
% 3.85/1.64  Subsumption          : 0.08
% 3.85/1.64  Abstraction          : 0.03
% 3.85/1.64  MUC search           : 0.00
% 3.85/1.64  Cooper               : 0.00
% 3.85/1.64  Total                : 0.90
% 3.85/1.64  Index Insertion      : 0.00
% 3.85/1.64  Index Deletion       : 0.00
% 3.85/1.64  Index Matching       : 0.00
% 3.85/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
