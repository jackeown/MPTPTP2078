%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 137 expanded)
%              Number of leaves         :   47 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 194 expanded)
%              Number of equality atoms :   43 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_228,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_147,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_221,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_175,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_160,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_184,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_116,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_144,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_118,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_153,plain,(
    ! [B_138] : k2_zfmisc_1(k1_xboole_0,B_138) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_88,plain,(
    ! [A_100,B_101] : v1_relat_1(k2_zfmisc_1(A_100,B_101)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_157,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_88])).

tff(c_86,plain,(
    ! [A_98,B_99] :
      ( v1_relat_1(k5_relat_1(A_98,B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_16,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [B_45] : k2_zfmisc_1(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1092,plain,(
    ! [A_248,B_249] :
      ( r2_hidden(k4_tarski('#skF_4'(A_248,B_249),'#skF_5'(A_248,B_249)),A_248)
      | r1_tarski(A_248,B_249)
      | ~ v1_relat_1(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_349,plain,(
    ! [B_171,A_172] :
      ( ~ r2_hidden(B_171,A_172)
      | k4_xboole_0(A_172,k1_tarski(B_171)) != A_172 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_358,plain,(
    ! [B_171] : ~ r2_hidden(B_171,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_349])).

tff(c_1100,plain,(
    ! [B_249] :
      ( r1_tarski(k1_xboole_0,B_249)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1092,c_358])).

tff(c_1105,plain,(
    ! [B_249] : r1_tarski(k1_xboole_0,B_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1100])).

tff(c_114,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_112,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1790,plain,(
    ! [A_285,B_286] :
      ( k1_relat_1(k5_relat_1(A_285,B_286)) = k1_relat_1(A_285)
      | ~ r1_tarski(k2_relat_1(A_285),k1_relat_1(B_286))
      | ~ v1_relat_1(B_286)
      | ~ v1_relat_1(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1805,plain,(
    ! [B_286] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_286)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_286))
      | ~ v1_relat_1(B_286)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1790])).

tff(c_1811,plain,(
    ! [B_287] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_287)) = k1_xboole_0
      | ~ v1_relat_1(B_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1105,c_114,c_1805])).

tff(c_96,plain,(
    ! [A_103] :
      ( k3_xboole_0(A_103,k2_zfmisc_1(k1_relat_1(A_103),k2_relat_1(A_103))) = A_103
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1823,plain,(
    ! [B_287] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_287),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_287)))) = k5_relat_1(k1_xboole_0,B_287)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_287))
      | ~ v1_relat_1(B_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1811,c_96])).

tff(c_1835,plain,(
    ! [B_288] :
      ( k5_relat_1(k1_xboole_0,B_288) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_288))
      | ~ v1_relat_1(B_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46,c_1823])).

tff(c_1839,plain,(
    ! [B_99] :
      ( k5_relat_1(k1_xboole_0,B_99) = k1_xboole_0
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_86,c_1835])).

tff(c_1843,plain,(
    ! [B_289] :
      ( k5_relat_1(k1_xboole_0,B_289) = k1_xboole_0
      | ~ v1_relat_1(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1839])).

tff(c_1861,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_1843])).

tff(c_1870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_1861])).

tff(c_1871,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_1925,plain,(
    ! [A_294,B_295] : v1_relat_1(k2_zfmisc_1(A_294,B_295)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1927,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1925])).

tff(c_44,plain,(
    ! [A_44] : k2_zfmisc_1(A_44,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2658,plain,(
    ! [A_391,B_392] :
      ( r2_hidden(k4_tarski('#skF_4'(A_391,B_392),'#skF_5'(A_391,B_392)),A_391)
      | r1_tarski(A_391,B_392)
      | ~ v1_relat_1(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2068,plain,(
    ! [B_323,A_324] :
      ( ~ r2_hidden(B_323,A_324)
      | k4_xboole_0(A_324,k1_tarski(B_323)) != A_324 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2077,plain,(
    ! [B_323] : ~ r2_hidden(B_323,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2068])).

tff(c_2666,plain,(
    ! [B_392] :
      ( r1_tarski(k1_xboole_0,B_392)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2658,c_2077])).

tff(c_2671,plain,(
    ! [B_392] : r1_tarski(k1_xboole_0,B_392) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_2666])).

tff(c_3049,plain,(
    ! [B_421,A_422] :
      ( k2_relat_1(k5_relat_1(B_421,A_422)) = k2_relat_1(A_422)
      | ~ r1_tarski(k1_relat_1(A_422),k2_relat_1(B_421))
      | ~ v1_relat_1(B_421)
      | ~ v1_relat_1(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_3061,plain,(
    ! [B_421] :
      ( k2_relat_1(k5_relat_1(B_421,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_421))
      | ~ v1_relat_1(B_421)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_3049])).

tff(c_3070,plain,(
    ! [B_423] :
      ( k2_relat_1(k5_relat_1(B_423,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_2671,c_112,c_3061])).

tff(c_3082,plain,(
    ! [B_423] :
      ( k3_xboole_0(k5_relat_1(B_423,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_423,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_423,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_423,k1_xboole_0))
      | ~ v1_relat_1(B_423) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3070,c_96])).

tff(c_3269,plain,(
    ! [B_431] :
      ( k5_relat_1(B_431,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_431,k1_xboole_0))
      | ~ v1_relat_1(B_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_44,c_3082])).

tff(c_3273,plain,(
    ! [A_98] :
      ( k5_relat_1(A_98,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_86,c_3269])).

tff(c_3277,plain,(
    ! [A_432] :
      ( k5_relat_1(A_432,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_432) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_3273])).

tff(c_3295,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_3277])).

tff(c_3304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1871,c_3295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:32:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/1.98  
% 5.26/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 5.26/1.98  
% 5.26/1.98  %Foreground sorts:
% 5.26/1.98  
% 5.26/1.98  
% 5.26/1.98  %Background operators:
% 5.26/1.98  
% 5.26/1.98  
% 5.26/1.98  %Foreground operators:
% 5.26/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.26/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.26/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.26/1.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.26/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.26/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.26/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.26/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.26/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.26/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.26/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.26/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.26/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.26/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.26/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.26/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.26/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.26/1.98  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.26/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.26/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.26/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.26/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.26/1.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.26/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.26/1.98  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.26/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.26/1.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.26/1.98  
% 5.26/2.00  tff(f_228, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 5.26/2.00  tff(f_85, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.26/2.00  tff(f_147, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.26/2.00  tff(f_145, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.26/2.00  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.26/2.00  tff(f_135, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 5.26/2.00  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.26/2.00  tff(f_96, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.26/2.00  tff(f_221, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.26/2.00  tff(f_175, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 5.26/2.00  tff(f_160, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 5.26/2.00  tff(f_184, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 5.26/2.00  tff(c_116, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_228])).
% 5.26/2.00  tff(c_144, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_116])).
% 5.26/2.00  tff(c_118, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_228])).
% 5.26/2.00  tff(c_153, plain, (![B_138]: (k2_zfmisc_1(k1_xboole_0, B_138)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/2.00  tff(c_88, plain, (![A_100, B_101]: (v1_relat_1(k2_zfmisc_1(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.26/2.00  tff(c_157, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_88])).
% 5.26/2.00  tff(c_86, plain, (![A_98, B_99]: (v1_relat_1(k5_relat_1(A_98, B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.26/2.00  tff(c_16, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.00  tff(c_46, plain, (![B_45]: (k2_zfmisc_1(k1_xboole_0, B_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/2.00  tff(c_1092, plain, (![A_248, B_249]: (r2_hidden(k4_tarski('#skF_4'(A_248, B_249), '#skF_5'(A_248, B_249)), A_248) | r1_tarski(A_248, B_249) | ~v1_relat_1(A_248))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.26/2.00  tff(c_18, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.00  tff(c_349, plain, (![B_171, A_172]: (~r2_hidden(B_171, A_172) | k4_xboole_0(A_172, k1_tarski(B_171))!=A_172)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.00  tff(c_358, plain, (![B_171]: (~r2_hidden(B_171, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_349])).
% 5.26/2.00  tff(c_1100, plain, (![B_249]: (r1_tarski(k1_xboole_0, B_249) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1092, c_358])).
% 5.26/2.00  tff(c_1105, plain, (![B_249]: (r1_tarski(k1_xboole_0, B_249))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1100])).
% 5.26/2.00  tff(c_114, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.26/2.00  tff(c_112, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.26/2.00  tff(c_1790, plain, (![A_285, B_286]: (k1_relat_1(k5_relat_1(A_285, B_286))=k1_relat_1(A_285) | ~r1_tarski(k2_relat_1(A_285), k1_relat_1(B_286)) | ~v1_relat_1(B_286) | ~v1_relat_1(A_285))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.26/2.00  tff(c_1805, plain, (![B_286]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_286))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_286)) | ~v1_relat_1(B_286) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1790])).
% 5.26/2.00  tff(c_1811, plain, (![B_287]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_287))=k1_xboole_0 | ~v1_relat_1(B_287))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1105, c_114, c_1805])).
% 5.26/2.00  tff(c_96, plain, (![A_103]: (k3_xboole_0(A_103, k2_zfmisc_1(k1_relat_1(A_103), k2_relat_1(A_103)))=A_103 | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.26/2.00  tff(c_1823, plain, (![B_287]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_287), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_287))))=k5_relat_1(k1_xboole_0, B_287) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_287)) | ~v1_relat_1(B_287))), inference(superposition, [status(thm), theory('equality')], [c_1811, c_96])).
% 5.26/2.00  tff(c_1835, plain, (![B_288]: (k5_relat_1(k1_xboole_0, B_288)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_288)) | ~v1_relat_1(B_288))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46, c_1823])).
% 5.26/2.00  tff(c_1839, plain, (![B_99]: (k5_relat_1(k1_xboole_0, B_99)=k1_xboole_0 | ~v1_relat_1(B_99) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_86, c_1835])).
% 5.26/2.00  tff(c_1843, plain, (![B_289]: (k5_relat_1(k1_xboole_0, B_289)=k1_xboole_0 | ~v1_relat_1(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1839])).
% 5.26/2.00  tff(c_1861, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_118, c_1843])).
% 5.26/2.00  tff(c_1870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_1861])).
% 5.26/2.00  tff(c_1871, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 5.26/2.00  tff(c_1925, plain, (![A_294, B_295]: (v1_relat_1(k2_zfmisc_1(A_294, B_295)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.26/2.00  tff(c_1927, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_1925])).
% 5.26/2.00  tff(c_44, plain, (![A_44]: (k2_zfmisc_1(A_44, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/2.00  tff(c_2658, plain, (![A_391, B_392]: (r2_hidden(k4_tarski('#skF_4'(A_391, B_392), '#skF_5'(A_391, B_392)), A_391) | r1_tarski(A_391, B_392) | ~v1_relat_1(A_391))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.26/2.00  tff(c_2068, plain, (![B_323, A_324]: (~r2_hidden(B_323, A_324) | k4_xboole_0(A_324, k1_tarski(B_323))!=A_324)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.00  tff(c_2077, plain, (![B_323]: (~r2_hidden(B_323, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2068])).
% 5.26/2.00  tff(c_2666, plain, (![B_392]: (r1_tarski(k1_xboole_0, B_392) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2658, c_2077])).
% 5.26/2.00  tff(c_2671, plain, (![B_392]: (r1_tarski(k1_xboole_0, B_392))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_2666])).
% 5.26/2.00  tff(c_3049, plain, (![B_421, A_422]: (k2_relat_1(k5_relat_1(B_421, A_422))=k2_relat_1(A_422) | ~r1_tarski(k1_relat_1(A_422), k2_relat_1(B_421)) | ~v1_relat_1(B_421) | ~v1_relat_1(A_422))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.26/2.00  tff(c_3061, plain, (![B_421]: (k2_relat_1(k5_relat_1(B_421, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_421)) | ~v1_relat_1(B_421) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_3049])).
% 5.26/2.00  tff(c_3070, plain, (![B_423]: (k2_relat_1(k5_relat_1(B_423, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_423))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_2671, c_112, c_3061])).
% 5.26/2.00  tff(c_3082, plain, (![B_423]: (k3_xboole_0(k5_relat_1(B_423, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_423, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_423, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_423, k1_xboole_0)) | ~v1_relat_1(B_423))), inference(superposition, [status(thm), theory('equality')], [c_3070, c_96])).
% 5.26/2.00  tff(c_3269, plain, (![B_431]: (k5_relat_1(B_431, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_431, k1_xboole_0)) | ~v1_relat_1(B_431))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_44, c_3082])).
% 5.26/2.00  tff(c_3273, plain, (![A_98]: (k5_relat_1(A_98, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_86, c_3269])).
% 5.26/2.00  tff(c_3277, plain, (![A_432]: (k5_relat_1(A_432, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_432))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_3273])).
% 5.26/2.00  tff(c_3295, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_118, c_3277])).
% 5.26/2.00  tff(c_3304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1871, c_3295])).
% 5.26/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.00  
% 5.26/2.00  Inference rules
% 5.26/2.00  ----------------------
% 5.26/2.00  #Ref     : 2
% 5.26/2.00  #Sup     : 735
% 5.26/2.00  #Fact    : 0
% 5.26/2.00  #Define  : 0
% 5.26/2.00  #Split   : 1
% 5.26/2.00  #Chain   : 0
% 5.26/2.00  #Close   : 0
% 5.26/2.00  
% 5.26/2.00  Ordering : KBO
% 5.26/2.00  
% 5.26/2.00  Simplification rules
% 5.26/2.00  ----------------------
% 5.26/2.00  #Subsume      : 18
% 5.26/2.00  #Demod        : 665
% 5.26/2.00  #Tautology    : 450
% 5.26/2.00  #SimpNegUnit  : 6
% 5.26/2.00  #BackRed      : 11
% 5.26/2.00  
% 5.26/2.00  #Partial instantiations: 0
% 5.26/2.00  #Strategies tried      : 1
% 5.26/2.00  
% 5.26/2.00  Timing (in seconds)
% 5.26/2.00  ----------------------
% 5.26/2.00  Preprocessing        : 0.48
% 5.26/2.00  Parsing              : 0.23
% 5.26/2.00  CNF conversion       : 0.05
% 5.26/2.00  Main loop            : 0.76
% 5.26/2.00  Inferencing          : 0.26
% 5.26/2.00  Reduction            : 0.28
% 5.26/2.00  Demodulation         : 0.20
% 5.26/2.00  BG Simplification    : 0.05
% 5.26/2.00  Subsumption          : 0.13
% 5.26/2.00  Abstraction          : 0.06
% 5.26/2.00  MUC search           : 0.00
% 5.26/2.00  Cooper               : 0.00
% 5.26/2.00  Total                : 1.28
% 5.26/2.00  Index Insertion      : 0.00
% 5.26/2.00  Index Deletion       : 0.00
% 5.26/2.00  Index Matching       : 0.00
% 5.26/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
