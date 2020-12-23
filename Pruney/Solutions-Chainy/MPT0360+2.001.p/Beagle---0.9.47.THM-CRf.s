%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 165 expanded)
%              Number of leaves         :   39 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 292 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_54,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ! [A_26] : k1_subset_1(A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_28] : k3_subset_1(A_28,k1_subset_1(A_28)) = k2_subset_1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [A_33] :
      ( r1_tarski(k1_subset_1(A_33),k3_subset_1(A_33,k1_subset_1(A_33)))
      | ~ m1_subset_1(k1_subset_1(A_33),k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    ! [A_33] :
      ( r1_tarski(k1_subset_1(A_33),k2_subset_1(A_33))
      | ~ m1_subset_1(k1_subset_1(A_33),k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_65,plain,(
    ! [A_33] :
      ( r1_tarski(k1_subset_1(A_33),A_33)
      | ~ m1_subset_1(k1_subset_1(A_33),k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_68,plain,(
    ! [A_33] :
      ( r1_tarski(k1_xboole_0,A_33)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_65])).

tff(c_70,plain,(
    ! [A_33] : r1_tarski(k1_xboole_0,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_205,plain,(
    ! [B_49,A_50] :
      ( v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_213,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_205])).

tff(c_217,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_1480,plain,(
    ! [B_157,A_158] :
      ( r2_hidden(B_157,A_158)
      | ~ m1_subset_1(B_157,A_158)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1565,plain,(
    ! [B_173,A_174] :
      ( r1_tarski(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_174))
      | v1_xboole_0(k1_zfmisc_1(A_174)) ) ),
    inference(resolution,[status(thm)],[c_1480,c_22])).

tff(c_1582,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_1565])).

tff(c_1590,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_1582])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1302,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = A_134
      | ~ r1_tarski(A_134,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1314,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_1302])).

tff(c_1415,plain,(
    ! [A_154,B_155] : k5_xboole_0(A_154,k3_xboole_0(A_154,B_155)) = k4_xboole_0(A_154,B_155) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1427,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_1415])).

tff(c_1434,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1427])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1439,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1434,c_18])).

tff(c_1442,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1439])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1398,plain,(
    ! [A_151,C_152,B_153] :
      ( r1_tarski(A_151,C_152)
      | ~ r1_tarski(k2_xboole_0(A_151,B_153),C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1509,plain,(
    ! [B_161,C_162,A_163] :
      ( r1_tarski(B_161,C_162)
      | ~ r1_tarski(k2_xboole_0(A_163,B_161),C_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1398])).

tff(c_1512,plain,(
    ! [C_162] :
      ( r1_tarski('#skF_5',C_162)
      | ~ r1_tarski('#skF_6',C_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1509])).

tff(c_24,plain,(
    ! [C_23,A_19] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_19))
      | ~ r1_tarski(C_23,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1383,plain,(
    ! [B_148,A_149] :
      ( m1_subset_1(B_148,A_149)
      | ~ r2_hidden(B_148,A_149)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1390,plain,(
    ! [C_23,A_19] :
      ( m1_subset_1(C_23,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19))
      | ~ r1_tarski(C_23,A_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_1383])).

tff(c_58,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1997,plain,(
    ! [C_203,A_204,B_205] :
      ( r1_tarski(C_203,k3_subset_1(A_204,B_205))
      | ~ r1_tarski(B_205,k3_subset_1(A_204,C_203))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_204))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(A_204)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2023,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_1997])).

tff(c_2039,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2023])).

tff(c_2096,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2039])).

tff(c_2099,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1390,c_2096])).

tff(c_2105,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_2099])).

tff(c_2112,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1512,c_2105])).

tff(c_2117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_2112])).

tff(c_2119,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2039])).

tff(c_2118,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2039])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1529,plain,(
    ! [C_164] :
      ( r1_tarski('#skF_5',C_164)
      | ~ r1_tarski('#skF_6',C_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1509])).

tff(c_52,plain,(
    ! [A_33,B_34] :
      ( k1_subset_1(A_33) = B_34
      | ~ r1_tarski(B_34,k3_subset_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    ! [B_34,A_33] :
      ( k1_xboole_0 = B_34
      | ~ r1_tarski(B_34,k3_subset_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_1533,plain,(
    ! [A_33] :
      ( k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_33))
      | ~ r1_tarski('#skF_6',k3_subset_1(A_33,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1529,c_66])).

tff(c_1539,plain,(
    ! [A_33] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_33))
      | ~ r1_tarski('#skF_6',k3_subset_1(A_33,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1533])).

tff(c_2137,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2118,c_1539])).

tff(c_2150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_2137])).

tff(c_2152,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_2185,plain,(
    ! [C_211,A_212] :
      ( r2_hidden(C_211,k1_zfmisc_1(A_212))
      | ~ r1_tarski(C_211,A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2195,plain,(
    ! [A_215,C_216] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_215))
      | ~ r1_tarski(C_216,A_215) ) ),
    inference(resolution,[status(thm)],[c_2185,c_4])).

tff(c_2199,plain,(
    ! [C_217] : ~ r1_tarski(C_217,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2152,c_2195])).

tff(c_2204,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_70,c_2199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.85/1.73  
% 3.85/1.73  %Foreground sorts:
% 3.85/1.73  
% 3.85/1.73  
% 3.85/1.73  %Background operators:
% 3.85/1.73  
% 3.85/1.73  
% 3.85/1.73  %Foreground operators:
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.85/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.85/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.85/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.73  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.85/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.85/1.73  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.85/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.85/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.85/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.85/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.73  
% 3.85/1.75  tff(f_94, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.85/1.75  tff(f_73, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.85/1.75  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.85/1.75  tff(f_77, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.85/1.75  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.85/1.75  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.85/1.75  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.85/1.75  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.85/1.75  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.85/1.75  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.85/1.75  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.85/1.75  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.85/1.75  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.85/1.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.85/1.75  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.85/1.75  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.85/1.75  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.85/1.75  tff(c_54, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.85/1.75  tff(c_42, plain, (![A_26]: (k1_subset_1(A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.75  tff(c_44, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.85/1.75  tff(c_46, plain, (![A_28]: (k3_subset_1(A_28, k1_subset_1(A_28))=k2_subset_1(A_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.75  tff(c_50, plain, (![A_33]: (r1_tarski(k1_subset_1(A_33), k3_subset_1(A_33, k1_subset_1(A_33))) | ~m1_subset_1(k1_subset_1(A_33), k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.85/1.75  tff(c_63, plain, (![A_33]: (r1_tarski(k1_subset_1(A_33), k2_subset_1(A_33)) | ~m1_subset_1(k1_subset_1(A_33), k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 3.85/1.75  tff(c_65, plain, (![A_33]: (r1_tarski(k1_subset_1(A_33), A_33) | ~m1_subset_1(k1_subset_1(A_33), k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 3.85/1.75  tff(c_68, plain, (![A_33]: (r1_tarski(k1_xboole_0, A_33) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_65])).
% 3.85/1.75  tff(c_70, plain, (![A_33]: (r1_tarski(k1_xboole_0, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 3.85/1.75  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.75  tff(c_205, plain, (![B_49, A_50]: (v1_xboole_0(B_49) | ~m1_subset_1(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.85/1.75  tff(c_213, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_205])).
% 3.85/1.75  tff(c_217, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_213])).
% 3.85/1.75  tff(c_1480, plain, (![B_157, A_158]: (r2_hidden(B_157, A_158) | ~m1_subset_1(B_157, A_158) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.85/1.75  tff(c_22, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.75  tff(c_1565, plain, (![B_173, A_174]: (r1_tarski(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(A_174)) | v1_xboole_0(k1_zfmisc_1(A_174)))), inference(resolution, [status(thm)], [c_1480, c_22])).
% 3.85/1.75  tff(c_1582, plain, (r1_tarski('#skF_6', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1565])).
% 3.85/1.75  tff(c_1590, plain, (r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_217, c_1582])).
% 3.85/1.75  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.75  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.75  tff(c_60, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.75  tff(c_1302, plain, (![A_134, B_135]: (k3_xboole_0(A_134, B_135)=A_134 | ~r1_tarski(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.85/1.75  tff(c_1314, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_1302])).
% 3.85/1.75  tff(c_1415, plain, (![A_154, B_155]: (k5_xboole_0(A_154, k3_xboole_0(A_154, B_155))=k4_xboole_0(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.75  tff(c_1427, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1314, c_1415])).
% 3.85/1.75  tff(c_1434, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1427])).
% 3.85/1.75  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.85/1.75  tff(c_1439, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1434, c_18])).
% 3.85/1.75  tff(c_1442, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1439])).
% 3.85/1.75  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.75  tff(c_1398, plain, (![A_151, C_152, B_153]: (r1_tarski(A_151, C_152) | ~r1_tarski(k2_xboole_0(A_151, B_153), C_152))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.75  tff(c_1509, plain, (![B_161, C_162, A_163]: (r1_tarski(B_161, C_162) | ~r1_tarski(k2_xboole_0(A_163, B_161), C_162))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1398])).
% 3.85/1.75  tff(c_1512, plain, (![C_162]: (r1_tarski('#skF_5', C_162) | ~r1_tarski('#skF_6', C_162))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1509])).
% 3.85/1.75  tff(c_24, plain, (![C_23, A_19]: (r2_hidden(C_23, k1_zfmisc_1(A_19)) | ~r1_tarski(C_23, A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.75  tff(c_1383, plain, (![B_148, A_149]: (m1_subset_1(B_148, A_149) | ~r2_hidden(B_148, A_149) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.85/1.75  tff(c_1390, plain, (![C_23, A_19]: (m1_subset_1(C_23, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)) | ~r1_tarski(C_23, A_19))), inference(resolution, [status(thm)], [c_24, c_1383])).
% 3.85/1.75  tff(c_58, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.75  tff(c_1997, plain, (![C_203, A_204, B_205]: (r1_tarski(C_203, k3_subset_1(A_204, B_205)) | ~r1_tarski(B_205, k3_subset_1(A_204, C_203)) | ~m1_subset_1(C_203, k1_zfmisc_1(A_204)) | ~m1_subset_1(B_205, k1_zfmisc_1(A_204)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.75  tff(c_2023, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1997])).
% 3.85/1.75  tff(c_2039, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2023])).
% 3.85/1.75  tff(c_2096, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2039])).
% 3.85/1.75  tff(c_2099, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1390, c_2096])).
% 3.85/1.75  tff(c_2105, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_217, c_2099])).
% 3.85/1.75  tff(c_2112, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1512, c_2105])).
% 3.85/1.75  tff(c_2117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1590, c_2112])).
% 3.85/1.75  tff(c_2119, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2039])).
% 3.85/1.75  tff(c_2118, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2039])).
% 3.85/1.75  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.75  tff(c_1529, plain, (![C_164]: (r1_tarski('#skF_5', C_164) | ~r1_tarski('#skF_6', C_164))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1509])).
% 3.85/1.75  tff(c_52, plain, (![A_33, B_34]: (k1_subset_1(A_33)=B_34 | ~r1_tarski(B_34, k3_subset_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.85/1.75  tff(c_66, plain, (![B_34, A_33]: (k1_xboole_0=B_34 | ~r1_tarski(B_34, k3_subset_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 3.85/1.75  tff(c_1533, plain, (![A_33]: (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_33)) | ~r1_tarski('#skF_6', k3_subset_1(A_33, '#skF_5')))), inference(resolution, [status(thm)], [c_1529, c_66])).
% 3.85/1.75  tff(c_1539, plain, (![A_33]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_33)) | ~r1_tarski('#skF_6', k3_subset_1(A_33, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1533])).
% 3.85/1.75  tff(c_2137, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_2118, c_1539])).
% 3.85/1.75  tff(c_2150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2119, c_2137])).
% 3.85/1.75  tff(c_2152, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_213])).
% 3.85/1.75  tff(c_2185, plain, (![C_211, A_212]: (r2_hidden(C_211, k1_zfmisc_1(A_212)) | ~r1_tarski(C_211, A_212))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.75  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.75  tff(c_2195, plain, (![A_215, C_216]: (~v1_xboole_0(k1_zfmisc_1(A_215)) | ~r1_tarski(C_216, A_215))), inference(resolution, [status(thm)], [c_2185, c_4])).
% 3.85/1.75  tff(c_2199, plain, (![C_217]: (~r1_tarski(C_217, '#skF_4'))), inference(resolution, [status(thm)], [c_2152, c_2195])).
% 3.85/1.75  tff(c_2204, plain, $false, inference(resolution, [status(thm)], [c_70, c_2199])).
% 3.85/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.75  
% 3.85/1.75  Inference rules
% 3.85/1.75  ----------------------
% 3.85/1.75  #Ref     : 0
% 3.85/1.75  #Sup     : 507
% 3.85/1.75  #Fact    : 0
% 3.85/1.75  #Define  : 0
% 3.85/1.75  #Split   : 10
% 3.85/1.75  #Chain   : 0
% 3.85/1.75  #Close   : 0
% 3.85/1.75  
% 3.85/1.75  Ordering : KBO
% 3.85/1.75  
% 3.85/1.75  Simplification rules
% 3.85/1.75  ----------------------
% 3.85/1.75  #Subsume      : 49
% 3.85/1.75  #Demod        : 200
% 3.85/1.75  #Tautology    : 269
% 3.85/1.75  #SimpNegUnit  : 32
% 3.85/1.75  #BackRed      : 5
% 3.85/1.75  
% 3.85/1.75  #Partial instantiations: 0
% 3.85/1.75  #Strategies tried      : 1
% 3.85/1.75  
% 3.85/1.75  Timing (in seconds)
% 3.85/1.75  ----------------------
% 3.85/1.76  Preprocessing        : 0.36
% 3.85/1.76  Parsing              : 0.19
% 3.85/1.76  CNF conversion       : 0.03
% 3.85/1.76  Main loop            : 0.58
% 3.85/1.76  Inferencing          : 0.21
% 3.85/1.76  Reduction            : 0.20
% 3.85/1.76  Demodulation         : 0.14
% 3.85/1.76  BG Simplification    : 0.03
% 3.85/1.76  Subsumption          : 0.10
% 3.85/1.76  Abstraction          : 0.02
% 3.85/1.76  MUC search           : 0.00
% 3.85/1.76  Cooper               : 0.00
% 3.85/1.76  Total                : 0.99
% 3.85/1.76  Index Insertion      : 0.00
% 4.18/1.76  Index Deletion       : 0.00
% 4.18/1.76  Index Matching       : 0.00
% 4.18/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
