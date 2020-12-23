%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 149 expanded)
%              Number of leaves         :   46 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 231 expanded)
%              Number of equality atoms :   55 ( 107 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_9 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_246,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_135,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_105,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_239,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_202,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_236,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_168,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_193,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_211,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_138,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_153,plain,(
    ! [B_91] : k2_zfmisc_1(k1_xboole_0,B_91) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [A_46,B_47] : v1_relat_1(k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_157,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_102])).

tff(c_100,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_136,plain,
    ( k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_189,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_36,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_225,plain,(
    ! [A_99,B_100] : k2_xboole_0(k1_tarski(A_99),B_100) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_229,plain,(
    ! [A_99] : k1_tarski(A_99) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_225])).

tff(c_449,plain,(
    ! [A_145,B_146] :
      ( k2_xboole_0(k1_tarski(A_145),B_146) = B_146
      | ~ r2_hidden(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_461,plain,(
    ! [A_145] :
      ( k1_tarski(A_145) = k1_xboole_0
      | ~ r2_hidden(A_145,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_36])).

tff(c_478,plain,(
    ! [A_145] : ~ r2_hidden(A_145,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_461])).

tff(c_40,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_132,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_7613,plain,(
    ! [A_10212,B_10213] :
      ( k1_relat_1(k5_relat_1(A_10212,B_10213)) = k1_relat_1(A_10212)
      | ~ r1_tarski(k2_relat_1(A_10212),k1_relat_1(B_10213))
      | ~ v1_relat_1(B_10213)
      | ~ v1_relat_1(A_10212) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_7629,plain,(
    ! [B_10213] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_10213)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_10213))
      | ~ v1_relat_1(B_10213)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_7613])).

tff(c_7637,plain,(
    ! [B_10294] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_10294)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_10294))
      | ~ v1_relat_1(B_10294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_134,c_7629])).

tff(c_7642,plain,(
    ! [B_10294] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_10294)) = k1_xboole_0
      | ~ v1_relat_1(B_10294)
      | k4_xboole_0(k1_xboole_0,k1_relat_1(B_10294)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_7637])).

tff(c_7711,plain,(
    ! [B_10455] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_10455)) = k1_xboole_0
      | ~ v1_relat_1(B_10455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7642])).

tff(c_795,plain,(
    ! [A_189] :
      ( k1_xboole_0 = A_189
      | r2_hidden(k4_tarski('#skF_10'(A_189),'#skF_11'(A_189)),A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_112,plain,(
    ! [A_57,C_59,B_58] :
      ( r2_hidden(A_57,k1_relat_1(C_59))
      | ~ r2_hidden(k4_tarski(A_57,B_58),C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_820,plain,(
    ! [A_189] :
      ( r2_hidden('#skF_10'(A_189),k1_relat_1(A_189))
      | k1_xboole_0 = A_189
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_795,c_112])).

tff(c_7750,plain,(
    ! [B_10455] :
      ( r2_hidden('#skF_10'(k5_relat_1(k1_xboole_0,B_10455)),k1_xboole_0)
      | k5_relat_1(k1_xboole_0,B_10455) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_10455))
      | ~ v1_relat_1(B_10455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7711,c_820])).

tff(c_7894,plain,(
    ! [B_10861] :
      ( k5_relat_1(k1_xboole_0,B_10861) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_10861))
      | ~ v1_relat_1(B_10861) ) ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_7750])).

tff(c_7903,plain,(
    ! [B_45] :
      ( k5_relat_1(k1_xboole_0,B_45) = k1_xboole_0
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_100,c_7894])).

tff(c_7909,plain,(
    ! [B_10942] :
      ( k5_relat_1(k1_xboole_0,B_10942) = k1_xboole_0
      | ~ v1_relat_1(B_10942) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_7903])).

tff(c_7921,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_7909])).

tff(c_7929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_7921])).

tff(c_7930,plain,(
    k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_7971,plain,(
    ! [A_11028,B_11029] : k2_xboole_0(k1_tarski(A_11028),B_11029) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7975,plain,(
    ! [A_11028] : k1_tarski(A_11028) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7971])).

tff(c_8236,plain,(
    ! [A_11073,B_11074] :
      ( k2_xboole_0(k1_tarski(A_11073),B_11074) = B_11074
      | ~ r2_hidden(A_11073,B_11074) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8245,plain,(
    ! [A_11073] :
      ( k1_tarski(A_11073) = k1_xboole_0
      | ~ r2_hidden(A_11073,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8236,c_36])).

tff(c_8262,plain,(
    ! [A_11073] : ~ r2_hidden(A_11073,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_7975,c_8245])).

tff(c_7931,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_8587,plain,(
    ! [A_11118,B_11119] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_11118,B_11119)),k2_relat_1(B_11119))
      | ~ v1_relat_1(B_11119)
      | ~ v1_relat_1(A_11118) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_8593,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7931,c_8587])).

tff(c_8599,plain,(
    r1_tarski(k1_xboole_0,k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_138,c_132,c_8593])).

tff(c_15709,plain,(
    ! [B_26408,A_26409] :
      ( k2_relat_1(k5_relat_1(B_26408,A_26409)) = k2_relat_1(A_26409)
      | ~ r1_tarski(k1_relat_1(A_26409),k2_relat_1(B_26408))
      | ~ v1_relat_1(B_26408)
      | ~ v1_relat_1(A_26409) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_15724,plain,(
    ! [B_26408] :
      ( k2_relat_1(k5_relat_1(B_26408,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_26408))
      | ~ v1_relat_1(B_26408)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_15709])).

tff(c_15735,plain,(
    ! [B_26530] :
      ( k2_relat_1(k5_relat_1(B_26530,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_26530))
      | ~ v1_relat_1(B_26530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_132,c_15724])).

tff(c_15744,plain,
    ( k2_relat_1(k5_relat_1('#skF_12',k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_8599,c_15735])).

tff(c_15755,plain,(
    k2_relat_1(k5_relat_1('#skF_12',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_15744])).

tff(c_130,plain,(
    ! [A_86] :
      ( k1_xboole_0 = A_86
      | r2_hidden(k4_tarski('#skF_10'(A_86),'#skF_11'(A_86)),A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_10937,plain,(
    ! [B_14292,C_14293,A_14294] :
      ( r2_hidden(B_14292,k2_relat_1(C_14293))
      | ~ r2_hidden(k4_tarski(A_14294,B_14292),C_14293)
      | ~ v1_relat_1(C_14293) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_10962,plain,(
    ! [A_86] :
      ( r2_hidden('#skF_11'(A_86),k2_relat_1(A_86))
      | k1_xboole_0 = A_86
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_130,c_10937])).

tff(c_15785,plain,
    ( r2_hidden('#skF_11'(k5_relat_1('#skF_12',k1_xboole_0)),k1_xboole_0)
    | k5_relat_1('#skF_12',k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1('#skF_12',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15755,c_10962])).

tff(c_15814,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_7930,c_8262,c_15785])).

tff(c_15829,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_100,c_15814])).

tff(c_15833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_157,c_15829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.63  
% 7.90/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.63  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_9 > #skF_12 > #skF_4
% 7.90/2.63  
% 7.90/2.63  %Foreground sorts:
% 7.90/2.63  
% 7.90/2.63  
% 7.90/2.63  %Background operators:
% 7.90/2.63  
% 7.90/2.63  
% 7.90/2.63  %Foreground operators:
% 7.90/2.63  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.90/2.63  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.90/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.90/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.90/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/2.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.90/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.90/2.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.90/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.90/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.90/2.63  tff('#skF_10', type, '#skF_10': $i > $i).
% 7.90/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.90/2.63  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.90/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.90/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.90/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.90/2.63  tff('#skF_11', type, '#skF_11': $i > $i).
% 7.90/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/2.63  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.90/2.63  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.90/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.90/2.63  tff('#skF_12', type, '#skF_12': $i).
% 7.90/2.63  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.90/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.90/2.63  
% 7.90/2.65  tff(f_246, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 7.90/2.65  tff(f_80, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.90/2.65  tff(f_135, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.90/2.65  tff(f_133, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.90/2.65  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.90/2.65  tff(f_105, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 7.90/2.65  tff(f_102, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 7.90/2.65  tff(f_61, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.90/2.65  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.90/2.65  tff(f_239, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.90/2.65  tff(f_202, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 7.90/2.65  tff(f_236, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 7.90/2.65  tff(f_168, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 7.90/2.65  tff(f_193, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 7.90/2.65  tff(f_211, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 7.90/2.65  tff(c_138, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_246])).
% 7.90/2.65  tff(c_153, plain, (![B_91]: (k2_zfmisc_1(k1_xboole_0, B_91)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.90/2.65  tff(c_102, plain, (![A_46, B_47]: (v1_relat_1(k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.90/2.65  tff(c_157, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_102])).
% 7.90/2.65  tff(c_100, plain, (![A_44, B_45]: (v1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.90/2.65  tff(c_136, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_246])).
% 7.90/2.65  tff(c_189, plain, (k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_136])).
% 7.90/2.65  tff(c_36, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.90/2.65  tff(c_225, plain, (![A_99, B_100]: (k2_xboole_0(k1_tarski(A_99), B_100)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.90/2.65  tff(c_229, plain, (![A_99]: (k1_tarski(A_99)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_225])).
% 7.90/2.65  tff(c_449, plain, (![A_145, B_146]: (k2_xboole_0(k1_tarski(A_145), B_146)=B_146 | ~r2_hidden(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.90/2.65  tff(c_461, plain, (![A_145]: (k1_tarski(A_145)=k1_xboole_0 | ~r2_hidden(A_145, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_449, c_36])).
% 7.90/2.65  tff(c_478, plain, (![A_145]: (~r2_hidden(A_145, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_229, c_461])).
% 7.90/2.65  tff(c_40, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.90/2.65  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.90/2.65  tff(c_134, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_239])).
% 7.90/2.65  tff(c_132, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_239])).
% 7.90/2.65  tff(c_7613, plain, (![A_10212, B_10213]: (k1_relat_1(k5_relat_1(A_10212, B_10213))=k1_relat_1(A_10212) | ~r1_tarski(k2_relat_1(A_10212), k1_relat_1(B_10213)) | ~v1_relat_1(B_10213) | ~v1_relat_1(A_10212))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.90/2.65  tff(c_7629, plain, (![B_10213]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_10213))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_10213)) | ~v1_relat_1(B_10213) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_7613])).
% 7.90/2.65  tff(c_7637, plain, (![B_10294]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_10294))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1(B_10294)) | ~v1_relat_1(B_10294))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_134, c_7629])).
% 7.90/2.65  tff(c_7642, plain, (![B_10294]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_10294))=k1_xboole_0 | ~v1_relat_1(B_10294) | k4_xboole_0(k1_xboole_0, k1_relat_1(B_10294))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_7637])).
% 7.90/2.65  tff(c_7711, plain, (![B_10455]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_10455))=k1_xboole_0 | ~v1_relat_1(B_10455))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7642])).
% 7.90/2.65  tff(c_795, plain, (![A_189]: (k1_xboole_0=A_189 | r2_hidden(k4_tarski('#skF_10'(A_189), '#skF_11'(A_189)), A_189) | ~v1_relat_1(A_189))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.65  tff(c_112, plain, (![A_57, C_59, B_58]: (r2_hidden(A_57, k1_relat_1(C_59)) | ~r2_hidden(k4_tarski(A_57, B_58), C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.90/2.65  tff(c_820, plain, (![A_189]: (r2_hidden('#skF_10'(A_189), k1_relat_1(A_189)) | k1_xboole_0=A_189 | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_795, c_112])).
% 7.90/2.65  tff(c_7750, plain, (![B_10455]: (r2_hidden('#skF_10'(k5_relat_1(k1_xboole_0, B_10455)), k1_xboole_0) | k5_relat_1(k1_xboole_0, B_10455)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_10455)) | ~v1_relat_1(B_10455))), inference(superposition, [status(thm), theory('equality')], [c_7711, c_820])).
% 7.90/2.65  tff(c_7894, plain, (![B_10861]: (k5_relat_1(k1_xboole_0, B_10861)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_10861)) | ~v1_relat_1(B_10861))), inference(negUnitSimplification, [status(thm)], [c_478, c_7750])).
% 7.90/2.65  tff(c_7903, plain, (![B_45]: (k5_relat_1(k1_xboole_0, B_45)=k1_xboole_0 | ~v1_relat_1(B_45) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_100, c_7894])).
% 7.90/2.65  tff(c_7909, plain, (![B_10942]: (k5_relat_1(k1_xboole_0, B_10942)=k1_xboole_0 | ~v1_relat_1(B_10942))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_7903])).
% 7.90/2.65  tff(c_7921, plain, (k5_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_7909])).
% 7.90/2.65  tff(c_7929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_7921])).
% 7.90/2.65  tff(c_7930, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_136])).
% 7.90/2.65  tff(c_7971, plain, (![A_11028, B_11029]: (k2_xboole_0(k1_tarski(A_11028), B_11029)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.90/2.65  tff(c_7975, plain, (![A_11028]: (k1_tarski(A_11028)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_7971])).
% 7.90/2.65  tff(c_8236, plain, (![A_11073, B_11074]: (k2_xboole_0(k1_tarski(A_11073), B_11074)=B_11074 | ~r2_hidden(A_11073, B_11074))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.90/2.65  tff(c_8245, plain, (![A_11073]: (k1_tarski(A_11073)=k1_xboole_0 | ~r2_hidden(A_11073, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8236, c_36])).
% 7.90/2.65  tff(c_8262, plain, (![A_11073]: (~r2_hidden(A_11073, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_7975, c_8245])).
% 7.90/2.65  tff(c_7931, plain, (k5_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_136])).
% 7.90/2.65  tff(c_8587, plain, (![A_11118, B_11119]: (r1_tarski(k2_relat_1(k5_relat_1(A_11118, B_11119)), k2_relat_1(B_11119)) | ~v1_relat_1(B_11119) | ~v1_relat_1(A_11118))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.90/2.65  tff(c_8593, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k2_relat_1('#skF_12')) | ~v1_relat_1('#skF_12') | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7931, c_8587])).
% 7.90/2.65  tff(c_8599, plain, (r1_tarski(k1_xboole_0, k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_138, c_132, c_8593])).
% 7.90/2.65  tff(c_15709, plain, (![B_26408, A_26409]: (k2_relat_1(k5_relat_1(B_26408, A_26409))=k2_relat_1(A_26409) | ~r1_tarski(k1_relat_1(A_26409), k2_relat_1(B_26408)) | ~v1_relat_1(B_26408) | ~v1_relat_1(A_26409))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.90/2.65  tff(c_15724, plain, (![B_26408]: (k2_relat_1(k5_relat_1(B_26408, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_26408)) | ~v1_relat_1(B_26408) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_15709])).
% 7.90/2.65  tff(c_15735, plain, (![B_26530]: (k2_relat_1(k5_relat_1(B_26530, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(B_26530)) | ~v1_relat_1(B_26530))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_132, c_15724])).
% 7.90/2.65  tff(c_15744, plain, (k2_relat_1(k5_relat_1('#skF_12', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_8599, c_15735])).
% 7.90/2.65  tff(c_15755, plain, (k2_relat_1(k5_relat_1('#skF_12', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_15744])).
% 7.90/2.65  tff(c_130, plain, (![A_86]: (k1_xboole_0=A_86 | r2_hidden(k4_tarski('#skF_10'(A_86), '#skF_11'(A_86)), A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.65  tff(c_10937, plain, (![B_14292, C_14293, A_14294]: (r2_hidden(B_14292, k2_relat_1(C_14293)) | ~r2_hidden(k4_tarski(A_14294, B_14292), C_14293) | ~v1_relat_1(C_14293))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.90/2.65  tff(c_10962, plain, (![A_86]: (r2_hidden('#skF_11'(A_86), k2_relat_1(A_86)) | k1_xboole_0=A_86 | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_130, c_10937])).
% 7.90/2.65  tff(c_15785, plain, (r2_hidden('#skF_11'(k5_relat_1('#skF_12', k1_xboole_0)), k1_xboole_0) | k5_relat_1('#skF_12', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_12', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15755, c_10962])).
% 7.90/2.65  tff(c_15814, plain, (~v1_relat_1(k5_relat_1('#skF_12', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_7930, c_8262, c_15785])).
% 7.90/2.65  tff(c_15829, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_100, c_15814])).
% 7.90/2.65  tff(c_15833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_157, c_15829])).
% 7.90/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.65  
% 7.90/2.65  Inference rules
% 7.90/2.65  ----------------------
% 7.90/2.65  #Ref     : 2
% 7.90/2.65  #Sup     : 1262
% 7.90/2.65  #Fact    : 0
% 7.90/2.65  #Define  : 0
% 7.90/2.65  #Split   : 11
% 7.90/2.65  #Chain   : 0
% 7.90/2.65  #Close   : 0
% 7.90/2.65  
% 7.90/2.65  Ordering : KBO
% 7.90/2.65  
% 7.90/2.65  Simplification rules
% 7.90/2.65  ----------------------
% 7.90/2.65  #Subsume      : 191
% 7.90/2.65  #Demod        : 673
% 7.90/2.65  #Tautology    : 565
% 7.90/2.65  #SimpNegUnit  : 89
% 7.90/2.65  #BackRed      : 4
% 7.90/2.65  
% 7.90/2.65  #Partial instantiations: 14903
% 7.90/2.65  #Strategies tried      : 1
% 7.90/2.65  
% 7.90/2.65  Timing (in seconds)
% 7.90/2.65  ----------------------
% 7.90/2.65  Preprocessing        : 0.39
% 7.90/2.65  Parsing              : 0.20
% 7.90/2.65  CNF conversion       : 0.03
% 7.90/2.65  Main loop            : 1.49
% 7.90/2.65  Inferencing          : 0.77
% 7.90/2.65  Reduction            : 0.38
% 7.90/2.65  Demodulation         : 0.27
% 7.90/2.65  BG Simplification    : 0.05
% 7.90/2.65  Subsumption          : 0.20
% 7.90/2.65  Abstraction          : 0.05
% 7.90/2.65  MUC search           : 0.00
% 7.90/2.65  Cooper               : 0.00
% 7.90/2.65  Total                : 1.92
% 7.90/2.65  Index Insertion      : 0.00
% 7.90/2.66  Index Deletion       : 0.00
% 7.90/2.66  Index Matching       : 0.00
% 7.90/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
