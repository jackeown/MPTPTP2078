%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0350+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 414 expanded)
%              Number of leaves         :   30 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 798 expanded)
%              Number of equality atoms :   43 ( 190 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_76,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_70,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_24,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_5335,plain,(
    ! [A_219,B_220] :
      ( k4_xboole_0(A_219,B_220) = k3_subset_1(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5349,plain,(
    ! [A_221] : k4_xboole_0(A_221,A_221) = k3_subset_1(A_221,A_221) ),
    inference(resolution,[status(thm)],[c_48,c_5335])).

tff(c_44,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_165,plain,(
    ! [B_38,A_39] :
      ( v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_177,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_165])).

tff(c_184,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_223,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_236,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_38])).

tff(c_292,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_185,plain,(
    ! [B_43,A_44] :
      ( r2_hidden(B_43,A_44)
      | ~ m1_subset_1(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_358,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | v1_xboole_0(k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_185,c_4])).

tff(c_374,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_358])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_292,c_374])).

tff(c_383,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_698,plain,(
    ! [A_101,B_102,C_103] :
      ( k4_subset_1(A_101,B_102,C_103) = k2_xboole_0(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4662,plain,(
    ! [A_196,B_197,B_198] :
      ( k4_subset_1(A_196,B_197,k3_subset_1(A_196,B_198)) = k2_xboole_0(B_197,k3_subset_1(A_196,B_198))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_196)) ) ),
    inference(resolution,[status(thm)],[c_30,c_698])).

tff(c_5104,plain,(
    ! [B_204] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_204)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_204))
      | ~ m1_subset_1(B_204,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_4662])).

tff(c_5127,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_5104])).

tff(c_5138,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_5127])).

tff(c_5140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_5138])).

tff(c_5141,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_42,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5146,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5141,c_42])).

tff(c_40,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5149,plain,(
    ! [A_24] : k4_xboole_0('#skF_4',A_24) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5146,c_5146,c_40])).

tff(c_5359,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5349,c_5149])).

tff(c_5142,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_176,plain,(
    ! [A_13] :
      ( v1_xboole_0(A_13)
      | ~ v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_48,c_165])).

tff(c_5158,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5142,c_176])).

tff(c_5194,plain,(
    ! [A_209] :
      ( A_209 = '#skF_4'
      | ~ v1_xboole_0(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5146,c_42])).

tff(c_5204,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5158,c_5194])).

tff(c_5210,plain,(
    k4_subset_1('#skF_4','#skF_4',k3_subset_1('#skF_4','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5204,c_5204,c_5204,c_47])).

tff(c_5369,plain,(
    k4_subset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5359,c_5210])).

tff(c_5205,plain,(
    k1_zfmisc_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5142,c_5194])).

tff(c_5218,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5204,c_5205])).

tff(c_5231,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5218,c_48])).

tff(c_36,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5150,plain,(
    ! [A_21] : k2_xboole_0(A_21,'#skF_4') = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5146,c_36])).

tff(c_6347,plain,(
    ! [A_277,B_278,C_279] :
      ( k4_subset_1(A_277,B_278,C_279) = k2_xboole_0(B_278,C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(A_277))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(A_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6353,plain,(
    ! [B_278,C_279] :
      ( k4_subset_1('#skF_4',B_278,C_279) = k2_xboole_0(B_278,C_279)
      | ~ m1_subset_1(C_279,'#skF_4')
      | ~ m1_subset_1(B_278,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5218,c_6347])).

tff(c_6364,plain,(
    ! [B_280,C_281] :
      ( k4_subset_1('#skF_4',B_280,C_281) = k2_xboole_0(B_280,C_281)
      | ~ m1_subset_1(C_281,'#skF_4')
      | ~ m1_subset_1(B_280,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5218,c_6353])).

tff(c_6370,plain,(
    ! [B_280] :
      ( k4_subset_1('#skF_4',B_280,'#skF_4') = k2_xboole_0(B_280,'#skF_4')
      | ~ m1_subset_1(B_280,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5231,c_6364])).

tff(c_6381,plain,(
    ! [B_282] :
      ( k4_subset_1('#skF_4',B_282,'#skF_4') = B_282
      | ~ m1_subset_1(B_282,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5150,c_6370])).

tff(c_6390,plain,(
    k4_subset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5231,c_6381])).

tff(c_6400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5369,c_6390])).

%------------------------------------------------------------------------------
