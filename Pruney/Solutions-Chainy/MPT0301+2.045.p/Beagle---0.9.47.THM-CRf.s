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
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 17.76s
% Output     : CNFRefutation 17.76s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 890 expanded)
%              Number of leaves         :   35 ( 281 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 (1736 expanded)
%              Number of equality atoms :  105 ( 951 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,k3_xboole_0(k2_zfmisc_1(B,C),k2_zfmisc_1(D,E)))
        & ! [F,G] :
            ~ ( A = k4_tarski(F,G)
              & r2_hidden(F,k3_xboole_0(B,D))
              & r2_hidden(G,k3_xboole_0(C,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

tff(f_107,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_110,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,(
    ! [A_13,C_56] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_118,plain,(
    ! [C_56] : ~ r2_hidden(C_56,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_116])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_521,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_hidden(k4_tarski(A_105,B_106),k2_zfmisc_1(C_107,D_108))
      | ~ r2_hidden(B_106,D_108)
      | ~ r2_hidden(A_105,C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_532,plain,(
    ! [A_105,B_106] :
      ( r2_hidden(k4_tarski(A_105,B_106),k1_xboole_0)
      | ~ r2_hidden(B_106,'#skF_12')
      | ~ r2_hidden(A_105,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_521])).

tff(c_536,plain,(
    ! [B_106,A_105] :
      ( ~ r2_hidden(B_106,'#skF_12')
      | ~ r2_hidden(A_105,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_532])).

tff(c_538,plain,(
    ! [A_109] : ~ r2_hidden(A_109,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_566,plain,(
    ! [B_110] : r1_xboole_0('#skF_11',B_110) ),
    inference(resolution,[status(thm)],[c_6,c_538])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_575,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_566,c_22])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_575])).

tff(c_583,plain,(
    ! [B_111] : ~ r2_hidden(B_111,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_611,plain,(
    ! [B_112] : r1_xboole_0('#skF_12',B_112) ),
    inference(resolution,[status(thm)],[c_6,c_583])).

tff(c_620,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_611,c_22])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_620])).

tff(c_627,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_629,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_631,plain,(
    ! [C_56] : ~ r2_hidden(C_56,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_118])).

tff(c_16,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_645,plain,(
    ! [A_113] : r1_tarski('#skF_10',A_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_16])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_649,plain,(
    ! [A_113] : k3_xboole_0('#skF_10',A_113) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_645,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4293,plain,(
    ! [A_285,B_288,E_284,D_286,C_287] :
      ( r2_hidden('#skF_8'(E_284,A_285,D_286,C_287,B_288),k3_xboole_0(C_287,E_284))
      | ~ r2_hidden(A_285,k3_xboole_0(k2_zfmisc_1(B_288,C_287),k2_zfmisc_1(D_286,E_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15398,plain,(
    ! [E_478,B_479,C_480,D_481] :
      ( r2_hidden('#skF_8'(E_478,'#skF_2'(k2_zfmisc_1(B_479,C_480),k2_zfmisc_1(D_481,E_478)),D_481,C_480,B_479),k3_xboole_0(C_480,E_478))
      | r1_xboole_0(k2_zfmisc_1(B_479,C_480),k2_zfmisc_1(D_481,E_478)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4293])).

tff(c_15483,plain,(
    ! [A_113,B_479,D_481] :
      ( r2_hidden('#skF_8'(A_113,'#skF_2'(k2_zfmisc_1(B_479,'#skF_10'),k2_zfmisc_1(D_481,A_113)),D_481,'#skF_10',B_479),'#skF_10')
      | r1_xboole_0(k2_zfmisc_1(B_479,'#skF_10'),k2_zfmisc_1(D_481,A_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_15398])).

tff(c_15511,plain,(
    ! [B_482,D_483,A_484] : r1_xboole_0(k2_zfmisc_1(B_482,'#skF_10'),k2_zfmisc_1(D_483,A_484)) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_15483])).

tff(c_635,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_22])).

tff(c_15544,plain,(
    ! [D_483] : k2_zfmisc_1(D_483,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_15511,c_635])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_120,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_630,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_120])).

tff(c_15549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15544,c_630])).

tff(c_15550,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_15555,plain,(
    ! [C_56] : ~ r2_hidden(C_56,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15550,c_118])).

tff(c_15572,plain,(
    ! [A_485] : r1_tarski('#skF_9',A_485) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15550,c_16])).

tff(c_15576,plain,(
    ! [A_485] : k3_xboole_0('#skF_9',A_485) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15572,c_12])).

tff(c_19507,plain,(
    ! [E_659,A_660,C_662,B_663,D_661] :
      ( r2_hidden('#skF_7'(E_659,A_660,D_661,C_662,B_663),k3_xboole_0(B_663,D_661))
      | ~ r2_hidden(A_660,k3_xboole_0(k2_zfmisc_1(B_663,C_662),k2_zfmisc_1(D_661,E_659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_27587,plain,(
    ! [E_810,B_811,C_812,D_813] :
      ( r2_hidden('#skF_7'(E_810,'#skF_2'(k2_zfmisc_1(B_811,C_812),k2_zfmisc_1(D_813,E_810)),D_813,C_812,B_811),k3_xboole_0(B_811,D_813))
      | r1_xboole_0(k2_zfmisc_1(B_811,C_812),k2_zfmisc_1(D_813,E_810)) ) ),
    inference(resolution,[status(thm)],[c_8,c_19507])).

tff(c_27665,plain,(
    ! [E_810,C_812,A_485] :
      ( r2_hidden('#skF_7'(E_810,'#skF_2'(k2_zfmisc_1('#skF_9',C_812),k2_zfmisc_1(A_485,E_810)),A_485,C_812,'#skF_9'),'#skF_9')
      | r1_xboole_0(k2_zfmisc_1('#skF_9',C_812),k2_zfmisc_1(A_485,E_810)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15576,c_27587])).

tff(c_27692,plain,(
    ! [C_814,A_815,E_816] : r1_xboole_0(k2_zfmisc_1('#skF_9',C_814),k2_zfmisc_1(A_815,E_816)) ),
    inference(negUnitSimplification,[status(thm)],[c_15555,c_27665])).

tff(c_15559,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15550,c_22])).

tff(c_27722,plain,(
    ! [E_816] : k2_zfmisc_1('#skF_9',E_816) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_27692,c_15559])).

tff(c_15554,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15550,c_120])).

tff(c_27727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27722,c_15554])).

tff(c_27729,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_28081,plain,(
    ! [A_862,B_863,C_864,D_865] :
      ( r2_hidden(k4_tarski(A_862,B_863),k2_zfmisc_1(C_864,D_865))
      | ~ r2_hidden(B_863,D_865)
      | ~ r2_hidden(A_862,C_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28092,plain,(
    ! [A_862,B_863] :
      ( r2_hidden(k4_tarski(A_862,B_863),k1_xboole_0)
      | ~ r2_hidden(B_863,'#skF_10')
      | ~ r2_hidden(A_862,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27729,c_28081])).

tff(c_28099,plain,(
    ! [B_863,A_862] :
      ( ~ r2_hidden(B_863,'#skF_10')
      | ~ r2_hidden(A_862,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_28092])).

tff(c_28102,plain,(
    ! [A_866] : ~ r2_hidden(A_866,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_28099])).

tff(c_28118,plain,(
    ! [B_867] : r1_xboole_0('#skF_9',B_867) ),
    inference(resolution,[status(thm)],[c_6,c_28102])).

tff(c_28130,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_28118,c_22])).

tff(c_28139,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28130,c_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28140,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28130,c_88])).

tff(c_27728,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_28095,plain,(
    ! [A_862,B_863] :
      ( r2_hidden(k4_tarski(A_862,B_863),k1_xboole_0)
      | ~ r2_hidden(B_863,'#skF_12')
      | ~ r2_hidden(A_862,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27728,c_28081])).

tff(c_28100,plain,(
    ! [B_863,A_862] :
      ( ~ r2_hidden(B_863,'#skF_12')
      | ~ r2_hidden(A_862,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_28095])).

tff(c_28325,plain,(
    ! [A_876] : ~ r2_hidden(A_876,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_28100])).

tff(c_28347,plain,(
    ! [A_1] : r1_xboole_0(A_1,'#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_28325])).

tff(c_28420,plain,(
    ! [A_885] :
      ( ~ r1_xboole_0(A_885,A_885)
      | A_885 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28130,c_22])).

tff(c_28432,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_28347,c_28420])).

tff(c_28462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28140,c_28432])).

tff(c_28464,plain,(
    ! [B_886] : ~ r2_hidden(B_886,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_28100])).

tff(c_28486,plain,(
    ! [A_1] : r1_xboole_0(A_1,'#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_28464])).

tff(c_28533,plain,(
    ! [A_894] :
      ( ~ r1_xboole_0(A_894,A_894)
      | A_894 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28130,c_22])).

tff(c_28545,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_28486,c_28533])).

tff(c_28575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28139,c_28545])).

tff(c_28577,plain,(
    ! [B_895] : ~ r2_hidden(B_895,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_28099])).

tff(c_28593,plain,(
    ! [B_896] : r1_xboole_0('#skF_10',B_896) ),
    inference(resolution,[status(thm)],[c_6,c_28577])).

tff(c_28605,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_28593,c_22])).

tff(c_28856,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28605,c_89])).

tff(c_28616,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28605,c_88])).

tff(c_54,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28621,plain,(
    k3_tarski('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28605,c_28605,c_54])).

tff(c_28647,plain,(
    ! [A_899,B_900] :
      ( r2_hidden('#skF_4'(A_899,B_900),A_899)
      | r2_hidden('#skF_5'(A_899,B_900),B_900)
      | k3_tarski(A_899) = B_900 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28606,plain,(
    ! [A_862] : ~ r2_hidden(A_862,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_28100])).

tff(c_28818,plain,(
    ! [A_910] :
      ( r2_hidden('#skF_4'(A_910,'#skF_11'),A_910)
      | k3_tarski(A_910) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_28647,c_28606])).

tff(c_28576,plain,(
    ! [B_863] : ~ r2_hidden(B_863,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_28099])).

tff(c_28830,plain,(
    k3_tarski('#skF_10') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_28818,c_28576])).

tff(c_28844,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28621,c_28830])).

tff(c_28846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28616,c_28844])).

tff(c_28868,plain,(
    ! [B_911] : ~ r2_hidden(B_911,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_28100])).

tff(c_28883,plain,(
    ! [A_1] : r1_xboole_0(A_1,'#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_28868])).

tff(c_29132,plain,(
    ! [A_926] :
      ( ~ r1_xboole_0(A_926,A_926)
      | A_926 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28605,c_22])).

tff(c_29144,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_28883,c_29132])).

tff(c_29174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28856,c_29144])).

tff(c_29176,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_29181,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_18])).

tff(c_29179,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_29176,c_14])).

tff(c_43151,plain,(
    ! [A_1297,B_1298,C_1299] :
      ( ~ r1_xboole_0(A_1297,B_1298)
      | ~ r2_hidden(C_1299,k3_xboole_0(A_1297,B_1298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_43165,plain,(
    ! [A_13,C_1299] :
      ( ~ r1_xboole_0(A_13,'#skF_12')
      | ~ r2_hidden(C_1299,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29179,c_43151])).

tff(c_43169,plain,(
    ! [C_1299] : ~ r2_hidden(C_1299,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29181,c_43165])).

tff(c_29180,plain,(
    ! [A_14] : r1_tarski('#skF_12',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_16])).

tff(c_43129,plain,(
    ! [A_1290,B_1291] :
      ( k3_xboole_0(A_1290,B_1291) = A_1290
      | ~ r1_tarski(A_1290,B_1291) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43133,plain,(
    ! [A_14] : k3_xboole_0('#skF_12',A_14) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_29180,c_43129])).

tff(c_46767,plain,(
    ! [D_1466,C_1467,E_1464,A_1465,B_1468] :
      ( r2_hidden('#skF_8'(E_1464,A_1465,D_1466,C_1467,B_1468),k3_xboole_0(C_1467,E_1464))
      | ~ r2_hidden(A_1465,k3_xboole_0(k2_zfmisc_1(B_1468,C_1467),k2_zfmisc_1(D_1466,E_1464))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_57872,plain,(
    ! [E_1658,B_1659,C_1660,D_1661] :
      ( r2_hidden('#skF_8'(E_1658,'#skF_2'(k2_zfmisc_1(B_1659,C_1660),k2_zfmisc_1(D_1661,E_1658)),D_1661,C_1660,B_1659),k3_xboole_0(C_1660,E_1658))
      | r1_xboole_0(k2_zfmisc_1(B_1659,C_1660),k2_zfmisc_1(D_1661,E_1658)) ) ),
    inference(resolution,[status(thm)],[c_8,c_46767])).

tff(c_57957,plain,(
    ! [A_14,B_1659,D_1661] :
      ( r2_hidden('#skF_8'(A_14,'#skF_2'(k2_zfmisc_1(B_1659,'#skF_12'),k2_zfmisc_1(D_1661,A_14)),D_1661,'#skF_12',B_1659),'#skF_12')
      | r1_xboole_0(k2_zfmisc_1(B_1659,'#skF_12'),k2_zfmisc_1(D_1661,A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43133,c_57872])).

tff(c_57985,plain,(
    ! [B_1662,D_1663,A_1664] : r1_xboole_0(k2_zfmisc_1(B_1662,'#skF_12'),k2_zfmisc_1(D_1663,A_1664)) ),
    inference(negUnitSimplification,[status(thm)],[c_43169,c_57957])).

tff(c_29178,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_22])).

tff(c_58018,plain,(
    ! [D_1663] : k2_zfmisc_1(D_1663,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_57985,c_29178])).

tff(c_29240,plain,(
    ! [A_938,B_939,C_940] :
      ( ~ r1_xboole_0(A_938,B_939)
      | ~ r2_hidden(C_940,k3_xboole_0(A_938,B_939)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_29254,plain,(
    ! [A_13,C_940] :
      ( ~ r1_xboole_0(A_13,'#skF_12')
      | ~ r2_hidden(C_940,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29179,c_29240])).

tff(c_29258,plain,(
    ! [C_940] : ~ r2_hidden(C_940,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29181,c_29254])).

tff(c_29217,plain,(
    ! [A_931,B_932] :
      ( k3_xboole_0(A_931,B_932) = A_931
      | ~ r1_tarski(A_931,B_932) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_29221,plain,(
    ! [A_14] : k3_xboole_0('#skF_12',A_14) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_29180,c_29217])).

tff(c_32446,plain,(
    ! [D_1090,C_1091,A_1089,B_1092,E_1088] :
      ( r2_hidden('#skF_7'(E_1088,A_1089,D_1090,C_1091,B_1092),k3_xboole_0(B_1092,D_1090))
      | ~ r2_hidden(A_1089,k3_xboole_0(k2_zfmisc_1(B_1092,C_1091),k2_zfmisc_1(D_1090,E_1088))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42970,plain,(
    ! [E_1283,B_1284,C_1285,D_1286] :
      ( r2_hidden('#skF_7'(E_1283,'#skF_2'(k2_zfmisc_1(B_1284,C_1285),k2_zfmisc_1(D_1286,E_1283)),D_1286,C_1285,B_1284),k3_xboole_0(B_1284,D_1286))
      | r1_xboole_0(k2_zfmisc_1(B_1284,C_1285),k2_zfmisc_1(D_1286,E_1283)) ) ),
    inference(resolution,[status(thm)],[c_8,c_32446])).

tff(c_43056,plain,(
    ! [E_1283,C_1285,A_14] :
      ( r2_hidden('#skF_7'(E_1283,'#skF_2'(k2_zfmisc_1('#skF_12',C_1285),k2_zfmisc_1(A_14,E_1283)),A_14,C_1285,'#skF_12'),'#skF_12')
      | r1_xboole_0(k2_zfmisc_1('#skF_12',C_1285),k2_zfmisc_1(A_14,E_1283)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29221,c_42970])).

tff(c_43085,plain,(
    ! [C_1287,A_1288,E_1289] : r1_xboole_0(k2_zfmisc_1('#skF_12',C_1287),k2_zfmisc_1(A_1288,E_1289)) ),
    inference(negUnitSimplification,[status(thm)],[c_29258,c_43056])).

tff(c_43115,plain,(
    ! [E_1289] : k2_zfmisc_1('#skF_12',E_1289) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_43085,c_29178])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_29210,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_29176,c_29176,c_58])).

tff(c_29211,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_29210])).

tff(c_29175,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_29194,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29176,c_29175])).

tff(c_29212,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29211,c_29194])).

tff(c_43120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43115,c_29212])).

tff(c_43121,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_29210])).

tff(c_43123,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43121,c_29194])).

tff(c_58023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58018,c_43123])).

tff(c_58025,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58036,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58025,c_58025,c_58025,c_62])).

tff(c_58037,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58036])).

tff(c_58029,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58025,c_18])).

tff(c_58049,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58037,c_58029])).

tff(c_58027,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58025,c_58025,c_14])).

tff(c_58056,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58037,c_58037,c_58027])).

tff(c_58098,plain,(
    ! [A_1674,B_1675,C_1676] :
      ( ~ r1_xboole_0(A_1674,B_1675)
      | ~ r2_hidden(C_1676,k3_xboole_0(A_1674,B_1675)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58108,plain,(
    ! [A_13,C_1676] :
      ( ~ r1_xboole_0(A_13,'#skF_9')
      | ~ r2_hidden(C_1676,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58056,c_58098])).

tff(c_58111,plain,(
    ! [C_1676] : ~ r2_hidden(C_1676,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58049,c_58108])).

tff(c_58028,plain,(
    ! [A_14] : r1_tarski('#skF_11',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58025,c_16])).

tff(c_58047,plain,(
    ! [A_14] : r1_tarski('#skF_9',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58037,c_58028])).

tff(c_58075,plain,(
    ! [A_1669,B_1670] :
      ( k3_xboole_0(A_1669,B_1670) = A_1669
      | ~ r1_tarski(A_1669,B_1670) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58079,plain,(
    ! [A_14] : k3_xboole_0('#skF_9',A_14) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_58047,c_58075])).

tff(c_61714,plain,(
    ! [D_1845,C_1846,B_1847,E_1843,A_1844] :
      ( r2_hidden('#skF_7'(E_1843,A_1844,D_1845,C_1846,B_1847),k3_xboole_0(B_1847,D_1845))
      | ~ r2_hidden(A_1844,k3_xboole_0(k2_zfmisc_1(B_1847,C_1846),k2_zfmisc_1(D_1845,E_1843))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70965,plain,(
    ! [E_2006,B_2007,C_2008,D_2009] :
      ( r2_hidden('#skF_7'(E_2006,'#skF_2'(k2_zfmisc_1(B_2007,C_2008),k2_zfmisc_1(D_2009,E_2006)),D_2009,C_2008,B_2007),k3_xboole_0(B_2007,D_2009))
      | r1_xboole_0(k2_zfmisc_1(B_2007,C_2008),k2_zfmisc_1(D_2009,E_2006)) ) ),
    inference(resolution,[status(thm)],[c_8,c_61714])).

tff(c_71046,plain,(
    ! [E_2006,C_2008,A_14] :
      ( r2_hidden('#skF_7'(E_2006,'#skF_2'(k2_zfmisc_1('#skF_9',C_2008),k2_zfmisc_1(A_14,E_2006)),A_14,C_2008,'#skF_9'),'#skF_9')
      | r1_xboole_0(k2_zfmisc_1('#skF_9',C_2008),k2_zfmisc_1(A_14,E_2006)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58079,c_70965])).

tff(c_71073,plain,(
    ! [C_2010,A_2011,E_2012] : r1_xboole_0(k2_zfmisc_1('#skF_9',C_2010),k2_zfmisc_1(A_2011,E_2012)) ),
    inference(negUnitSimplification,[status(thm)],[c_58111,c_71046])).

tff(c_58026,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58025,c_22])).

tff(c_58065,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58037,c_58026])).

tff(c_71103,plain,(
    ! [E_2012] : k2_zfmisc_1('#skF_9',E_2012) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_71073,c_58065])).

tff(c_58038,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58037,c_58025])).

tff(c_58024,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58064,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58038,c_58024])).

tff(c_71108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71103,c_58064])).

tff(c_71109,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58036])).

tff(c_71128,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71109,c_58029])).

tff(c_71133,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71109,c_71109,c_58027])).

tff(c_71175,plain,(
    ! [A_2024,B_2025,C_2026] :
      ( ~ r1_xboole_0(A_2024,B_2025)
      | ~ r2_hidden(C_2026,k3_xboole_0(A_2024,B_2025)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71189,plain,(
    ! [A_13,C_2026] :
      ( ~ r1_xboole_0(A_13,'#skF_10')
      | ~ r2_hidden(C_2026,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71133,c_71175])).

tff(c_71193,plain,(
    ! [C_2026] : ~ r2_hidden(C_2026,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71128,c_71189])).

tff(c_71130,plain,(
    ! [A_14] : r1_tarski('#skF_10',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71109,c_58028])).

tff(c_71150,plain,(
    ! [A_2017,B_2018] :
      ( k3_xboole_0(A_2017,B_2018) = A_2017
      | ~ r1_tarski(A_2017,B_2018) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71154,plain,(
    ! [A_14] : k3_xboole_0('#skF_10',A_14) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_71130,c_71150])).

tff(c_74583,plain,(
    ! [B_2184,E_2180,C_2183,D_2182,A_2181] :
      ( r2_hidden('#skF_8'(E_2180,A_2181,D_2182,C_2183,B_2184),k3_xboole_0(C_2183,E_2180))
      | ~ r2_hidden(A_2181,k3_xboole_0(k2_zfmisc_1(B_2184,C_2183),k2_zfmisc_1(D_2182,E_2180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_84042,plain,(
    ! [E_2354,B_2355,C_2356,D_2357] :
      ( r2_hidden('#skF_8'(E_2354,'#skF_2'(k2_zfmisc_1(B_2355,C_2356),k2_zfmisc_1(D_2357,E_2354)),D_2357,C_2356,B_2355),k3_xboole_0(C_2356,E_2354))
      | r1_xboole_0(k2_zfmisc_1(B_2355,C_2356),k2_zfmisc_1(D_2357,E_2354)) ) ),
    inference(resolution,[status(thm)],[c_8,c_74583])).

tff(c_84123,plain,(
    ! [A_14,B_2355,D_2357] :
      ( r2_hidden('#skF_8'(A_14,'#skF_2'(k2_zfmisc_1(B_2355,'#skF_10'),k2_zfmisc_1(D_2357,A_14)),D_2357,'#skF_10',B_2355),'#skF_10')
      | r1_xboole_0(k2_zfmisc_1(B_2355,'#skF_10'),k2_zfmisc_1(D_2357,A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71154,c_84042])).

tff(c_84150,plain,(
    ! [B_2358,D_2359,A_2360] : r1_xboole_0(k2_zfmisc_1(B_2358,'#skF_10'),k2_zfmisc_1(D_2359,A_2360)) ),
    inference(negUnitSimplification,[status(thm)],[c_71193,c_84123])).

tff(c_71141,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | A_16 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71109,c_58026])).

tff(c_84180,plain,(
    ! [D_2359] : k2_zfmisc_1(D_2359,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_84150,c_71141])).

tff(c_71111,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71109,c_58025])).

tff(c_71132,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71111,c_58024])).

tff(c_84185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84180,c_71132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.76/9.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.76/9.63  
% 17.76/9.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.76/9.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 17.76/9.64  
% 17.76/9.64  %Foreground sorts:
% 17.76/9.64  
% 17.76/9.64  
% 17.76/9.64  %Background operators:
% 17.76/9.64  
% 17.76/9.64  
% 17.76/9.64  %Foreground operators:
% 17.76/9.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.76/9.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.76/9.64  tff('#skF_11', type, '#skF_11': $i).
% 17.76/9.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.76/9.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.76/9.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.76/9.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.76/9.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.76/9.64  tff('#skF_10', type, '#skF_10': $i).
% 17.76/9.64  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i) > $i).
% 17.76/9.64  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 17.76/9.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.76/9.64  tff('#skF_9', type, '#skF_9': $i).
% 17.76/9.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.76/9.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.76/9.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.76/9.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.76/9.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.76/9.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.76/9.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.76/9.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 17.76/9.64  tff('#skF_12', type, '#skF_12': $i).
% 17.76/9.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.76/9.64  
% 17.76/9.67  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 17.76/9.67  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 17.76/9.67  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 17.76/9.67  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 17.76/9.67  tff(f_114, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 17.76/9.67  tff(f_95, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 17.76/9.67  tff(f_79, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 17.76/9.67  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.76/9.67  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.76/9.67  tff(f_106, axiom, (![A, B, C, D, E]: ~(r2_hidden(A, k3_xboole_0(k2_zfmisc_1(B, C), k2_zfmisc_1(D, E))) & (![F, G]: ~(((A = k4_tarski(F, G)) & r2_hidden(F, k3_xboole_0(B, D))) & r2_hidden(G, k3_xboole_0(C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 17.76/9.67  tff(f_107, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 17.76/9.67  tff(f_89, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 17.76/9.67  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.76/9.67  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.76/9.67  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.76/9.67  tff(c_110, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_116, plain, (![A_13, C_56]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 17.76/9.67  tff(c_118, plain, (![C_56]: (~r2_hidden(C_56, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_116])).
% 17.76/9.67  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_89, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_56])).
% 17.76/9.67  tff(c_60, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_88, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_60])).
% 17.76/9.67  tff(c_66, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_133, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 17.76/9.67  tff(c_521, plain, (![A_105, B_106, C_107, D_108]: (r2_hidden(k4_tarski(A_105, B_106), k2_zfmisc_1(C_107, D_108)) | ~r2_hidden(B_106, D_108) | ~r2_hidden(A_105, C_107))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.76/9.67  tff(c_532, plain, (![A_105, B_106]: (r2_hidden(k4_tarski(A_105, B_106), k1_xboole_0) | ~r2_hidden(B_106, '#skF_12') | ~r2_hidden(A_105, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_521])).
% 17.76/9.67  tff(c_536, plain, (![B_106, A_105]: (~r2_hidden(B_106, '#skF_12') | ~r2_hidden(A_105, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_118, c_532])).
% 17.76/9.67  tff(c_538, plain, (![A_109]: (~r2_hidden(A_109, '#skF_11'))), inference(splitLeft, [status(thm)], [c_536])).
% 17.76/9.67  tff(c_566, plain, (![B_110]: (r1_xboole_0('#skF_11', B_110))), inference(resolution, [status(thm)], [c_6, c_538])).
% 17.76/9.67  tff(c_22, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.76/9.67  tff(c_575, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_566, c_22])).
% 17.76/9.67  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_575])).
% 17.76/9.67  tff(c_583, plain, (![B_111]: (~r2_hidden(B_111, '#skF_12'))), inference(splitRight, [status(thm)], [c_536])).
% 17.76/9.67  tff(c_611, plain, (![B_112]: (r1_xboole_0('#skF_12', B_112))), inference(resolution, [status(thm)], [c_6, c_583])).
% 17.76/9.67  tff(c_620, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_611, c_22])).
% 17.76/9.67  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_620])).
% 17.76/9.67  tff(c_627, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_66])).
% 17.76/9.67  tff(c_629, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_627])).
% 17.76/9.67  tff(c_631, plain, (![C_56]: (~r2_hidden(C_56, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_118])).
% 17.76/9.67  tff(c_16, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.76/9.67  tff(c_645, plain, (![A_113]: (r1_tarski('#skF_10', A_113))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_16])).
% 17.76/9.67  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.76/9.67  tff(c_649, plain, (![A_113]: (k3_xboole_0('#skF_10', A_113)='#skF_10')), inference(resolution, [status(thm)], [c_645, c_12])).
% 17.76/9.67  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_4293, plain, (![A_285, B_288, E_284, D_286, C_287]: (r2_hidden('#skF_8'(E_284, A_285, D_286, C_287, B_288), k3_xboole_0(C_287, E_284)) | ~r2_hidden(A_285, k3_xboole_0(k2_zfmisc_1(B_288, C_287), k2_zfmisc_1(D_286, E_284))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_15398, plain, (![E_478, B_479, C_480, D_481]: (r2_hidden('#skF_8'(E_478, '#skF_2'(k2_zfmisc_1(B_479, C_480), k2_zfmisc_1(D_481, E_478)), D_481, C_480, B_479), k3_xboole_0(C_480, E_478)) | r1_xboole_0(k2_zfmisc_1(B_479, C_480), k2_zfmisc_1(D_481, E_478)))), inference(resolution, [status(thm)], [c_8, c_4293])).
% 17.76/9.67  tff(c_15483, plain, (![A_113, B_479, D_481]: (r2_hidden('#skF_8'(A_113, '#skF_2'(k2_zfmisc_1(B_479, '#skF_10'), k2_zfmisc_1(D_481, A_113)), D_481, '#skF_10', B_479), '#skF_10') | r1_xboole_0(k2_zfmisc_1(B_479, '#skF_10'), k2_zfmisc_1(D_481, A_113)))), inference(superposition, [status(thm), theory('equality')], [c_649, c_15398])).
% 17.76/9.67  tff(c_15511, plain, (![B_482, D_483, A_484]: (r1_xboole_0(k2_zfmisc_1(B_482, '#skF_10'), k2_zfmisc_1(D_483, A_484)))), inference(negUnitSimplification, [status(thm)], [c_631, c_15483])).
% 17.76/9.67  tff(c_635, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_629, c_22])).
% 17.76/9.67  tff(c_15544, plain, (![D_483]: (k2_zfmisc_1(D_483, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_15511, c_635])).
% 17.76/9.67  tff(c_64, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_120, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 17.76/9.67  tff(c_630, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_629, c_120])).
% 17.76/9.67  tff(c_15549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15544, c_630])).
% 17.76/9.67  tff(c_15550, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_627])).
% 17.76/9.67  tff(c_15555, plain, (![C_56]: (~r2_hidden(C_56, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_15550, c_118])).
% 17.76/9.67  tff(c_15572, plain, (![A_485]: (r1_tarski('#skF_9', A_485))), inference(demodulation, [status(thm), theory('equality')], [c_15550, c_16])).
% 17.76/9.67  tff(c_15576, plain, (![A_485]: (k3_xboole_0('#skF_9', A_485)='#skF_9')), inference(resolution, [status(thm)], [c_15572, c_12])).
% 17.76/9.67  tff(c_19507, plain, (![E_659, A_660, C_662, B_663, D_661]: (r2_hidden('#skF_7'(E_659, A_660, D_661, C_662, B_663), k3_xboole_0(B_663, D_661)) | ~r2_hidden(A_660, k3_xboole_0(k2_zfmisc_1(B_663, C_662), k2_zfmisc_1(D_661, E_659))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_27587, plain, (![E_810, B_811, C_812, D_813]: (r2_hidden('#skF_7'(E_810, '#skF_2'(k2_zfmisc_1(B_811, C_812), k2_zfmisc_1(D_813, E_810)), D_813, C_812, B_811), k3_xboole_0(B_811, D_813)) | r1_xboole_0(k2_zfmisc_1(B_811, C_812), k2_zfmisc_1(D_813, E_810)))), inference(resolution, [status(thm)], [c_8, c_19507])).
% 17.76/9.67  tff(c_27665, plain, (![E_810, C_812, A_485]: (r2_hidden('#skF_7'(E_810, '#skF_2'(k2_zfmisc_1('#skF_9', C_812), k2_zfmisc_1(A_485, E_810)), A_485, C_812, '#skF_9'), '#skF_9') | r1_xboole_0(k2_zfmisc_1('#skF_9', C_812), k2_zfmisc_1(A_485, E_810)))), inference(superposition, [status(thm), theory('equality')], [c_15576, c_27587])).
% 17.76/9.67  tff(c_27692, plain, (![C_814, A_815, E_816]: (r1_xboole_0(k2_zfmisc_1('#skF_9', C_814), k2_zfmisc_1(A_815, E_816)))), inference(negUnitSimplification, [status(thm)], [c_15555, c_27665])).
% 17.76/9.67  tff(c_15559, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15550, c_22])).
% 17.76/9.67  tff(c_27722, plain, (![E_816]: (k2_zfmisc_1('#skF_9', E_816)='#skF_9')), inference(resolution, [status(thm)], [c_27692, c_15559])).
% 17.76/9.67  tff(c_15554, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15550, c_120])).
% 17.76/9.67  tff(c_27727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27722, c_15554])).
% 17.76/9.67  tff(c_27729, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 17.76/9.67  tff(c_28081, plain, (![A_862, B_863, C_864, D_865]: (r2_hidden(k4_tarski(A_862, B_863), k2_zfmisc_1(C_864, D_865)) | ~r2_hidden(B_863, D_865) | ~r2_hidden(A_862, C_864))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.76/9.67  tff(c_28092, plain, (![A_862, B_863]: (r2_hidden(k4_tarski(A_862, B_863), k1_xboole_0) | ~r2_hidden(B_863, '#skF_10') | ~r2_hidden(A_862, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_27729, c_28081])).
% 17.76/9.67  tff(c_28099, plain, (![B_863, A_862]: (~r2_hidden(B_863, '#skF_10') | ~r2_hidden(A_862, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_118, c_28092])).
% 17.76/9.67  tff(c_28102, plain, (![A_866]: (~r2_hidden(A_866, '#skF_9'))), inference(splitLeft, [status(thm)], [c_28099])).
% 17.76/9.67  tff(c_28118, plain, (![B_867]: (r1_xboole_0('#skF_9', B_867))), inference(resolution, [status(thm)], [c_6, c_28102])).
% 17.76/9.67  tff(c_28130, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_28118, c_22])).
% 17.76/9.67  tff(c_28139, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_28130, c_89])).
% 17.76/9.67  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.76/9.67  tff(c_28140, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_28130, c_88])).
% 17.76/9.67  tff(c_27728, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 17.76/9.67  tff(c_28095, plain, (![A_862, B_863]: (r2_hidden(k4_tarski(A_862, B_863), k1_xboole_0) | ~r2_hidden(B_863, '#skF_12') | ~r2_hidden(A_862, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_27728, c_28081])).
% 17.76/9.67  tff(c_28100, plain, (![B_863, A_862]: (~r2_hidden(B_863, '#skF_12') | ~r2_hidden(A_862, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_118, c_28095])).
% 17.76/9.67  tff(c_28325, plain, (![A_876]: (~r2_hidden(A_876, '#skF_11'))), inference(splitLeft, [status(thm)], [c_28100])).
% 17.76/9.67  tff(c_28347, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_11'))), inference(resolution, [status(thm)], [c_4, c_28325])).
% 17.76/9.67  tff(c_28420, plain, (![A_885]: (~r1_xboole_0(A_885, A_885) | A_885='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28130, c_22])).
% 17.76/9.67  tff(c_28432, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_28347, c_28420])).
% 17.76/9.67  tff(c_28462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28140, c_28432])).
% 17.76/9.67  tff(c_28464, plain, (![B_886]: (~r2_hidden(B_886, '#skF_12'))), inference(splitRight, [status(thm)], [c_28100])).
% 17.76/9.67  tff(c_28486, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_12'))), inference(resolution, [status(thm)], [c_4, c_28464])).
% 17.76/9.67  tff(c_28533, plain, (![A_894]: (~r1_xboole_0(A_894, A_894) | A_894='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28130, c_22])).
% 17.76/9.67  tff(c_28545, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_28486, c_28533])).
% 17.76/9.67  tff(c_28575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28139, c_28545])).
% 17.76/9.67  tff(c_28577, plain, (![B_895]: (~r2_hidden(B_895, '#skF_10'))), inference(splitRight, [status(thm)], [c_28099])).
% 17.76/9.67  tff(c_28593, plain, (![B_896]: (r1_xboole_0('#skF_10', B_896))), inference(resolution, [status(thm)], [c_6, c_28577])).
% 17.76/9.67  tff(c_28605, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_28593, c_22])).
% 17.76/9.67  tff(c_28856, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_28605, c_89])).
% 17.76/9.67  tff(c_28616, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_28605, c_88])).
% 17.76/9.67  tff(c_54, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.76/9.67  tff(c_28621, plain, (k3_tarski('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_28605, c_28605, c_54])).
% 17.76/9.67  tff(c_28647, plain, (![A_899, B_900]: (r2_hidden('#skF_4'(A_899, B_900), A_899) | r2_hidden('#skF_5'(A_899, B_900), B_900) | k3_tarski(A_899)=B_900)), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.76/9.67  tff(c_28606, plain, (![A_862]: (~r2_hidden(A_862, '#skF_11'))), inference(splitLeft, [status(thm)], [c_28100])).
% 17.76/9.67  tff(c_28818, plain, (![A_910]: (r2_hidden('#skF_4'(A_910, '#skF_11'), A_910) | k3_tarski(A_910)='#skF_11')), inference(resolution, [status(thm)], [c_28647, c_28606])).
% 17.76/9.67  tff(c_28576, plain, (![B_863]: (~r2_hidden(B_863, '#skF_10'))), inference(splitRight, [status(thm)], [c_28099])).
% 17.76/9.67  tff(c_28830, plain, (k3_tarski('#skF_10')='#skF_11'), inference(resolution, [status(thm)], [c_28818, c_28576])).
% 17.76/9.67  tff(c_28844, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_28621, c_28830])).
% 17.76/9.67  tff(c_28846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28616, c_28844])).
% 17.76/9.67  tff(c_28868, plain, (![B_911]: (~r2_hidden(B_911, '#skF_12'))), inference(splitRight, [status(thm)], [c_28100])).
% 17.76/9.67  tff(c_28883, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_12'))), inference(resolution, [status(thm)], [c_4, c_28868])).
% 17.76/9.67  tff(c_29132, plain, (![A_926]: (~r1_xboole_0(A_926, A_926) | A_926='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_28605, c_22])).
% 17.76/9.67  tff(c_29144, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_28883, c_29132])).
% 17.76/9.67  tff(c_29174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28856, c_29144])).
% 17.76/9.67  tff(c_29176, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_56])).
% 17.76/9.67  tff(c_29181, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_18])).
% 17.76/9.67  tff(c_29179, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_29176, c_14])).
% 17.76/9.67  tff(c_43151, plain, (![A_1297, B_1298, C_1299]: (~r1_xboole_0(A_1297, B_1298) | ~r2_hidden(C_1299, k3_xboole_0(A_1297, B_1298)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_43165, plain, (![A_13, C_1299]: (~r1_xboole_0(A_13, '#skF_12') | ~r2_hidden(C_1299, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_29179, c_43151])).
% 17.76/9.67  tff(c_43169, plain, (![C_1299]: (~r2_hidden(C_1299, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_29181, c_43165])).
% 17.76/9.67  tff(c_29180, plain, (![A_14]: (r1_tarski('#skF_12', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_16])).
% 17.76/9.67  tff(c_43129, plain, (![A_1290, B_1291]: (k3_xboole_0(A_1290, B_1291)=A_1290 | ~r1_tarski(A_1290, B_1291))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.76/9.67  tff(c_43133, plain, (![A_14]: (k3_xboole_0('#skF_12', A_14)='#skF_12')), inference(resolution, [status(thm)], [c_29180, c_43129])).
% 17.76/9.67  tff(c_46767, plain, (![D_1466, C_1467, E_1464, A_1465, B_1468]: (r2_hidden('#skF_8'(E_1464, A_1465, D_1466, C_1467, B_1468), k3_xboole_0(C_1467, E_1464)) | ~r2_hidden(A_1465, k3_xboole_0(k2_zfmisc_1(B_1468, C_1467), k2_zfmisc_1(D_1466, E_1464))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_57872, plain, (![E_1658, B_1659, C_1660, D_1661]: (r2_hidden('#skF_8'(E_1658, '#skF_2'(k2_zfmisc_1(B_1659, C_1660), k2_zfmisc_1(D_1661, E_1658)), D_1661, C_1660, B_1659), k3_xboole_0(C_1660, E_1658)) | r1_xboole_0(k2_zfmisc_1(B_1659, C_1660), k2_zfmisc_1(D_1661, E_1658)))), inference(resolution, [status(thm)], [c_8, c_46767])).
% 17.76/9.67  tff(c_57957, plain, (![A_14, B_1659, D_1661]: (r2_hidden('#skF_8'(A_14, '#skF_2'(k2_zfmisc_1(B_1659, '#skF_12'), k2_zfmisc_1(D_1661, A_14)), D_1661, '#skF_12', B_1659), '#skF_12') | r1_xboole_0(k2_zfmisc_1(B_1659, '#skF_12'), k2_zfmisc_1(D_1661, A_14)))), inference(superposition, [status(thm), theory('equality')], [c_43133, c_57872])).
% 17.76/9.67  tff(c_57985, plain, (![B_1662, D_1663, A_1664]: (r1_xboole_0(k2_zfmisc_1(B_1662, '#skF_12'), k2_zfmisc_1(D_1663, A_1664)))), inference(negUnitSimplification, [status(thm)], [c_43169, c_57957])).
% 17.76/9.67  tff(c_29178, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_22])).
% 17.76/9.67  tff(c_58018, plain, (![D_1663]: (k2_zfmisc_1(D_1663, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_57985, c_29178])).
% 17.76/9.67  tff(c_29240, plain, (![A_938, B_939, C_940]: (~r1_xboole_0(A_938, B_939) | ~r2_hidden(C_940, k3_xboole_0(A_938, B_939)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_29254, plain, (![A_13, C_940]: (~r1_xboole_0(A_13, '#skF_12') | ~r2_hidden(C_940, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_29179, c_29240])).
% 17.76/9.67  tff(c_29258, plain, (![C_940]: (~r2_hidden(C_940, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_29181, c_29254])).
% 17.76/9.67  tff(c_29217, plain, (![A_931, B_932]: (k3_xboole_0(A_931, B_932)=A_931 | ~r1_tarski(A_931, B_932))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.76/9.67  tff(c_29221, plain, (![A_14]: (k3_xboole_0('#skF_12', A_14)='#skF_12')), inference(resolution, [status(thm)], [c_29180, c_29217])).
% 17.76/9.67  tff(c_32446, plain, (![D_1090, C_1091, A_1089, B_1092, E_1088]: (r2_hidden('#skF_7'(E_1088, A_1089, D_1090, C_1091, B_1092), k3_xboole_0(B_1092, D_1090)) | ~r2_hidden(A_1089, k3_xboole_0(k2_zfmisc_1(B_1092, C_1091), k2_zfmisc_1(D_1090, E_1088))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_42970, plain, (![E_1283, B_1284, C_1285, D_1286]: (r2_hidden('#skF_7'(E_1283, '#skF_2'(k2_zfmisc_1(B_1284, C_1285), k2_zfmisc_1(D_1286, E_1283)), D_1286, C_1285, B_1284), k3_xboole_0(B_1284, D_1286)) | r1_xboole_0(k2_zfmisc_1(B_1284, C_1285), k2_zfmisc_1(D_1286, E_1283)))), inference(resolution, [status(thm)], [c_8, c_32446])).
% 17.76/9.67  tff(c_43056, plain, (![E_1283, C_1285, A_14]: (r2_hidden('#skF_7'(E_1283, '#skF_2'(k2_zfmisc_1('#skF_12', C_1285), k2_zfmisc_1(A_14, E_1283)), A_14, C_1285, '#skF_12'), '#skF_12') | r1_xboole_0(k2_zfmisc_1('#skF_12', C_1285), k2_zfmisc_1(A_14, E_1283)))), inference(superposition, [status(thm), theory('equality')], [c_29221, c_42970])).
% 17.76/9.67  tff(c_43085, plain, (![C_1287, A_1288, E_1289]: (r1_xboole_0(k2_zfmisc_1('#skF_12', C_1287), k2_zfmisc_1(A_1288, E_1289)))), inference(negUnitSimplification, [status(thm)], [c_29258, c_43056])).
% 17.76/9.67  tff(c_43115, plain, (![E_1289]: (k2_zfmisc_1('#skF_12', E_1289)='#skF_12')), inference(resolution, [status(thm)], [c_43085, c_29178])).
% 17.76/9.67  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_29210, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_29176, c_29176, c_58])).
% 17.76/9.67  tff(c_29211, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_29210])).
% 17.76/9.67  tff(c_29175, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 17.76/9.67  tff(c_29194, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_29176, c_29175])).
% 17.76/9.67  tff(c_29212, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_29211, c_29194])).
% 17.76/9.67  tff(c_43120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43115, c_29212])).
% 17.76/9.67  tff(c_43121, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_29210])).
% 17.76/9.67  tff(c_43123, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_43121, c_29194])).
% 17.76/9.67  tff(c_58023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58018, c_43123])).
% 17.76/9.67  tff(c_58025, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_60])).
% 17.76/9.67  tff(c_62, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.76/9.67  tff(c_58036, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_58025, c_58025, c_58025, c_62])).
% 17.76/9.67  tff(c_58037, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_58036])).
% 17.76/9.67  tff(c_58029, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_58025, c_18])).
% 17.76/9.67  tff(c_58049, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58037, c_58029])).
% 17.76/9.67  tff(c_58027, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_58025, c_58025, c_14])).
% 17.76/9.67  tff(c_58056, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_58037, c_58037, c_58027])).
% 17.76/9.67  tff(c_58098, plain, (![A_1674, B_1675, C_1676]: (~r1_xboole_0(A_1674, B_1675) | ~r2_hidden(C_1676, k3_xboole_0(A_1674, B_1675)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_58108, plain, (![A_13, C_1676]: (~r1_xboole_0(A_13, '#skF_9') | ~r2_hidden(C_1676, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_58056, c_58098])).
% 17.76/9.67  tff(c_58111, plain, (![C_1676]: (~r2_hidden(C_1676, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58049, c_58108])).
% 17.76/9.67  tff(c_58028, plain, (![A_14]: (r1_tarski('#skF_11', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_58025, c_16])).
% 17.76/9.67  tff(c_58047, plain, (![A_14]: (r1_tarski('#skF_9', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_58037, c_58028])).
% 17.76/9.67  tff(c_58075, plain, (![A_1669, B_1670]: (k3_xboole_0(A_1669, B_1670)=A_1669 | ~r1_tarski(A_1669, B_1670))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.76/9.67  tff(c_58079, plain, (![A_14]: (k3_xboole_0('#skF_9', A_14)='#skF_9')), inference(resolution, [status(thm)], [c_58047, c_58075])).
% 17.76/9.67  tff(c_61714, plain, (![D_1845, C_1846, B_1847, E_1843, A_1844]: (r2_hidden('#skF_7'(E_1843, A_1844, D_1845, C_1846, B_1847), k3_xboole_0(B_1847, D_1845)) | ~r2_hidden(A_1844, k3_xboole_0(k2_zfmisc_1(B_1847, C_1846), k2_zfmisc_1(D_1845, E_1843))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_70965, plain, (![E_2006, B_2007, C_2008, D_2009]: (r2_hidden('#skF_7'(E_2006, '#skF_2'(k2_zfmisc_1(B_2007, C_2008), k2_zfmisc_1(D_2009, E_2006)), D_2009, C_2008, B_2007), k3_xboole_0(B_2007, D_2009)) | r1_xboole_0(k2_zfmisc_1(B_2007, C_2008), k2_zfmisc_1(D_2009, E_2006)))), inference(resolution, [status(thm)], [c_8, c_61714])).
% 17.76/9.67  tff(c_71046, plain, (![E_2006, C_2008, A_14]: (r2_hidden('#skF_7'(E_2006, '#skF_2'(k2_zfmisc_1('#skF_9', C_2008), k2_zfmisc_1(A_14, E_2006)), A_14, C_2008, '#skF_9'), '#skF_9') | r1_xboole_0(k2_zfmisc_1('#skF_9', C_2008), k2_zfmisc_1(A_14, E_2006)))), inference(superposition, [status(thm), theory('equality')], [c_58079, c_70965])).
% 17.76/9.67  tff(c_71073, plain, (![C_2010, A_2011, E_2012]: (r1_xboole_0(k2_zfmisc_1('#skF_9', C_2010), k2_zfmisc_1(A_2011, E_2012)))), inference(negUnitSimplification, [status(thm)], [c_58111, c_71046])).
% 17.76/9.67  tff(c_58026, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_58025, c_22])).
% 17.76/9.67  tff(c_58065, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_58037, c_58026])).
% 17.76/9.67  tff(c_71103, plain, (![E_2012]: (k2_zfmisc_1('#skF_9', E_2012)='#skF_9')), inference(resolution, [status(thm)], [c_71073, c_58065])).
% 17.76/9.67  tff(c_58038, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_58037, c_58025])).
% 17.76/9.67  tff(c_58024, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 17.76/9.67  tff(c_58064, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_58038, c_58024])).
% 17.76/9.67  tff(c_71108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71103, c_58064])).
% 17.76/9.67  tff(c_71109, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_58036])).
% 17.76/9.67  tff(c_71128, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_71109, c_58029])).
% 17.76/9.67  tff(c_71133, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_71109, c_71109, c_58027])).
% 17.76/9.67  tff(c_71175, plain, (![A_2024, B_2025, C_2026]: (~r1_xboole_0(A_2024, B_2025) | ~r2_hidden(C_2026, k3_xboole_0(A_2024, B_2025)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.76/9.67  tff(c_71189, plain, (![A_13, C_2026]: (~r1_xboole_0(A_13, '#skF_10') | ~r2_hidden(C_2026, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_71133, c_71175])).
% 17.76/9.67  tff(c_71193, plain, (![C_2026]: (~r2_hidden(C_2026, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_71128, c_71189])).
% 17.76/9.67  tff(c_71130, plain, (![A_14]: (r1_tarski('#skF_10', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_71109, c_58028])).
% 17.76/9.67  tff(c_71150, plain, (![A_2017, B_2018]: (k3_xboole_0(A_2017, B_2018)=A_2017 | ~r1_tarski(A_2017, B_2018))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.76/9.67  tff(c_71154, plain, (![A_14]: (k3_xboole_0('#skF_10', A_14)='#skF_10')), inference(resolution, [status(thm)], [c_71130, c_71150])).
% 17.76/9.67  tff(c_74583, plain, (![B_2184, E_2180, C_2183, D_2182, A_2181]: (r2_hidden('#skF_8'(E_2180, A_2181, D_2182, C_2183, B_2184), k3_xboole_0(C_2183, E_2180)) | ~r2_hidden(A_2181, k3_xboole_0(k2_zfmisc_1(B_2184, C_2183), k2_zfmisc_1(D_2182, E_2180))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.76/9.67  tff(c_84042, plain, (![E_2354, B_2355, C_2356, D_2357]: (r2_hidden('#skF_8'(E_2354, '#skF_2'(k2_zfmisc_1(B_2355, C_2356), k2_zfmisc_1(D_2357, E_2354)), D_2357, C_2356, B_2355), k3_xboole_0(C_2356, E_2354)) | r1_xboole_0(k2_zfmisc_1(B_2355, C_2356), k2_zfmisc_1(D_2357, E_2354)))), inference(resolution, [status(thm)], [c_8, c_74583])).
% 17.76/9.67  tff(c_84123, plain, (![A_14, B_2355, D_2357]: (r2_hidden('#skF_8'(A_14, '#skF_2'(k2_zfmisc_1(B_2355, '#skF_10'), k2_zfmisc_1(D_2357, A_14)), D_2357, '#skF_10', B_2355), '#skF_10') | r1_xboole_0(k2_zfmisc_1(B_2355, '#skF_10'), k2_zfmisc_1(D_2357, A_14)))), inference(superposition, [status(thm), theory('equality')], [c_71154, c_84042])).
% 17.76/9.67  tff(c_84150, plain, (![B_2358, D_2359, A_2360]: (r1_xboole_0(k2_zfmisc_1(B_2358, '#skF_10'), k2_zfmisc_1(D_2359, A_2360)))), inference(negUnitSimplification, [status(thm)], [c_71193, c_84123])).
% 17.76/9.67  tff(c_71141, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | A_16='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_71109, c_58026])).
% 17.76/9.67  tff(c_84180, plain, (![D_2359]: (k2_zfmisc_1(D_2359, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_84150, c_71141])).
% 17.76/9.67  tff(c_71111, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_71109, c_58025])).
% 17.76/9.67  tff(c_71132, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_71111, c_58024])).
% 17.76/9.67  tff(c_84185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84180, c_71132])).
% 17.76/9.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.76/9.67  
% 17.76/9.67  Inference rules
% 17.76/9.67  ----------------------
% 17.76/9.67  #Ref     : 0
% 17.76/9.67  #Sup     : 22511
% 17.76/9.67  #Fact    : 0
% 17.76/9.67  #Define  : 0
% 17.76/9.67  #Split   : 16
% 17.76/9.67  #Chain   : 0
% 17.76/9.67  #Close   : 0
% 17.76/9.67  
% 17.76/9.67  Ordering : KBO
% 17.76/9.67  
% 17.76/9.67  Simplification rules
% 17.76/9.67  ----------------------
% 17.76/9.67  #Subsume      : 9274
% 17.76/9.67  #Demod        : 26249
% 17.76/9.67  #Tautology    : 6324
% 17.76/9.67  #SimpNegUnit  : 1184
% 17.76/9.67  #BackRed      : 94
% 17.76/9.67  
% 17.76/9.67  #Partial instantiations: 0
% 17.76/9.67  #Strategies tried      : 1
% 17.76/9.67  
% 17.76/9.67  Timing (in seconds)
% 17.76/9.67  ----------------------
% 18.04/9.67  Preprocessing        : 0.34
% 18.04/9.67  Parsing              : 0.18
% 18.04/9.67  CNF conversion       : 0.03
% 18.04/9.67  Main loop            : 8.46
% 18.04/9.67  Inferencing          : 1.90
% 18.04/9.67  Reduction            : 2.09
% 18.04/9.67  Demodulation         : 1.53
% 18.04/9.67  BG Simplification    : 0.19
% 18.04/9.67  Subsumption          : 3.93
% 18.04/9.67  Abstraction          : 0.36
% 18.04/9.67  MUC search           : 0.00
% 18.04/9.67  Cooper               : 0.00
% 18.04/9.67  Total                : 8.87
% 18.04/9.67  Index Insertion      : 0.00
% 18.04/9.67  Index Deletion       : 0.00
% 18.04/9.67  Index Matching       : 0.00
% 18.04/9.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
