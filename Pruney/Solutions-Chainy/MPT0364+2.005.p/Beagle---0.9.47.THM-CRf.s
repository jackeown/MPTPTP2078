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
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 8.50s
% Output     : CNFRefutation 8.57s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 252 expanded)
%              Number of leaves         :   36 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  131 ( 317 expanded)
%              Number of equality atoms :   51 ( 152 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_157,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_270,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_68])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_695,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_711,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_695])).

tff(c_28,plain,(
    ! [A_27,C_29,B_28] :
      ( r1_xboole_0(A_27,k4_xboole_0(C_29,B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1072,plain,(
    ! [A_118] :
      ( r1_xboole_0(A_118,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_118,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_28])).

tff(c_1080,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1072,c_157])).

tff(c_1086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_1080])).

tff(c_1087,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_33] : k5_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1271,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1297,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1271])).

tff(c_1328,plain,(
    ! [A_146] : k4_xboole_0(A_146,A_146) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1297])).

tff(c_1333,plain,(
    ! [A_146] : k4_xboole_0(A_146,k1_xboole_0) = k3_xboole_0(A_146,A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_20])).

tff(c_1337,plain,(
    ! [A_146] : k4_xboole_0(A_146,k1_xboole_0) = A_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1333])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1234,plain,(
    ! [B_136,A_137] :
      ( r2_hidden(B_136,A_137)
      | ~ m1_subset_1(B_136,A_137)
      | v1_xboole_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [C_38,A_34] :
      ( r1_tarski(C_38,A_34)
      | ~ r2_hidden(C_38,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1238,plain,(
    ! [B_136,A_34] :
      ( r1_tarski(B_136,A_34)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_34))
      | v1_xboole_0(k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_1234,c_34])).

tff(c_1242,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1238])).

tff(c_1255,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1242])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1256,plain,(
    ! [A_140,B_141] : k4_xboole_0(A_140,k4_xboole_0(A_140,B_141)) = k3_xboole_0(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1265,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1256])).

tff(c_7946,plain,(
    ! [A_309,B_310] : k3_xboole_0(A_309,k4_xboole_0(A_309,B_310)) = k4_xboole_0(A_309,B_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1265])).

tff(c_1482,plain,(
    ! [A_151,C_152,B_153] :
      ( r1_xboole_0(A_151,k4_xboole_0(C_152,B_153))
      | ~ r1_tarski(A_151,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1501,plain,(
    ! [A_151,C_152,B_153] :
      ( k3_xboole_0(A_151,k4_xboole_0(C_152,B_153)) = k1_xboole_0
      | ~ r1_tarski(A_151,B_153) ) ),
    inference(resolution,[status(thm)],[c_1482,c_6])).

tff(c_8165,plain,(
    ! [A_311,B_312] :
      ( k4_xboole_0(A_311,B_312) = k1_xboole_0
      | ~ r1_tarski(A_311,B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7946,c_1501])).

tff(c_8245,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1255,c_8165])).

tff(c_8318,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8245,c_20])).

tff(c_8344,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_8318])).

tff(c_1088,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2806,plain,(
    ! [A_206,B_207] :
      ( k4_xboole_0(A_206,B_207) = k3_subset_1(A_206,B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2822,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2806])).

tff(c_26,plain,(
    ! [B_25,A_24,C_26] :
      ( r1_xboole_0(B_25,k4_xboole_0(A_24,C_26))
      | ~ r1_xboole_0(A_24,k4_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11568,plain,(
    ! [A_336] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_336,'#skF_5'))
      | ~ r1_xboole_0(A_336,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2822,c_26])).

tff(c_11638,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1088,c_11568])).

tff(c_11652,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11638,c_6])).

tff(c_11718,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11652,c_18])).

tff(c_11749,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_11718])).

tff(c_105,plain,(
    ! [A_49,B_50] : r1_tarski(k3_xboole_0(A_49,B_50),A_49) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_1301,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1297])).

tff(c_1586,plain,(
    ! [A_156,A_157] :
      ( r1_xboole_0(A_156,k1_xboole_0)
      | ~ r1_tarski(A_156,A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_1482])).

tff(c_1603,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_108,c_1586])).

tff(c_1919,plain,(
    ! [B_177,A_178,C_179] :
      ( r1_xboole_0(B_177,k4_xboole_0(A_178,C_179))
      | ~ r1_xboole_0(A_178,k4_xboole_0(B_177,C_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1934,plain,(
    ! [A_7,A_178] :
      ( r1_xboole_0(A_7,k4_xboole_0(A_178,A_7))
      | ~ r1_xboole_0(A_178,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_1919])).

tff(c_1950,plain,(
    ! [A_180,A_181] : r1_xboole_0(A_180,k4_xboole_0(A_181,A_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_1934])).

tff(c_2170,plain,(
    ! [A_188,A_189] : k3_xboole_0(A_188,k4_xboole_0(A_189,A_188)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1950,c_6])).

tff(c_2187,plain,(
    ! [A_188,A_189] : k4_xboole_0(A_188,k4_xboole_0(A_189,A_188)) = k4_xboole_0(A_188,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2170,c_18])).

tff(c_2228,plain,(
    ! [A_188,A_189] : k4_xboole_0(A_188,k4_xboole_0(A_189,A_188)) = A_188 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_2187])).

tff(c_1982,plain,(
    ! [A_180,A_181] : k3_xboole_0(A_180,k4_xboole_0(A_181,A_180)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1950,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2918,plain,(
    ! [A_208,B_209,C_210] : k5_xboole_0(k3_xboole_0(A_208,B_209),k3_xboole_0(C_210,B_209)) = k3_xboole_0(k5_xboole_0(A_208,C_210),B_209) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2940,plain,(
    ! [A_208,B_209] : k3_xboole_0(k5_xboole_0(A_208,k3_xboole_0(A_208,B_209)),B_209) = k4_xboole_0(k3_xboole_0(A_208,B_209),B_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2918,c_12])).

tff(c_3042,plain,(
    ! [A_211,B_212] : k4_xboole_0(k3_xboole_0(A_211,B_212),B_212) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_2,c_12,c_2940])).

tff(c_3058,plain,(
    ! [A_211,B_212,A_24] :
      ( r1_xboole_0(k3_xboole_0(A_211,B_212),k4_xboole_0(A_24,B_212))
      | ~ r1_xboole_0(A_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3042,c_26])).

tff(c_4168,plain,(
    ! [A_236,B_237,A_238] : r1_xboole_0(k3_xboole_0(A_236,B_237),k4_xboole_0(A_238,B_237)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_3058])).

tff(c_4216,plain,(
    ! [A_236,A_189,A_188] : r1_xboole_0(k3_xboole_0(A_236,k4_xboole_0(A_189,A_188)),A_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_2228,c_4168])).

tff(c_13233,plain,(
    ! [A_367] : r1_xboole_0(k3_xboole_0(A_367,'#skF_3'),k4_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11749,c_4216])).

tff(c_13248,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8344,c_13233])).

tff(c_13289,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13248,c_6])).

tff(c_13372,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13289,c_12])).

tff(c_13409,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_13372])).

tff(c_1139,plain,(
    ! [B_120,A_121] : k3_xboole_0(B_120,A_121) = k3_xboole_0(A_121,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1154,plain,(
    ! [B_120,A_121] : r1_tarski(k3_xboole_0(B_120,A_121),A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_16])).

tff(c_13932,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13409,c_1154])).

tff(c_13958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1087,c_13932])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.50/3.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.06  
% 8.57/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.57/3.06  
% 8.57/3.06  %Foreground sorts:
% 8.57/3.06  
% 8.57/3.06  
% 8.57/3.06  %Background operators:
% 8.57/3.06  
% 8.57/3.06  
% 8.57/3.06  %Foreground operators:
% 8.57/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.57/3.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.57/3.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.57/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.57/3.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.57/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.57/3.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.57/3.06  tff('#skF_5', type, '#skF_5': $i).
% 8.57/3.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.57/3.06  tff('#skF_3', type, '#skF_3': $i).
% 8.57/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.57/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.57/3.06  tff('#skF_4', type, '#skF_4': $i).
% 8.57/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.57/3.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.57/3.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.57/3.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.57/3.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.57/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.57/3.06  
% 8.57/3.08  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 8.57/3.08  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.57/3.08  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 8.57/3.08  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.57/3.08  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.57/3.08  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.57/3.08  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.57/3.08  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.57/3.08  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.57/3.08  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 8.57/3.08  tff(f_72, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.57/3.08  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.57/3.08  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.57/3.08  tff(f_57, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 8.57/3.08  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.57/3.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.57/3.08  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.57/3.08  tff(c_62, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.57/3.08  tff(c_157, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_62])).
% 8.57/3.08  tff(c_68, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.57/3.08  tff(c_270, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_157, c_68])).
% 8.57/3.08  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.57/3.08  tff(c_695, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.57/3.08  tff(c_711, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_695])).
% 8.57/3.08  tff(c_28, plain, (![A_27, C_29, B_28]: (r1_xboole_0(A_27, k4_xboole_0(C_29, B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.57/3.08  tff(c_1072, plain, (![A_118]: (r1_xboole_0(A_118, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_118, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_711, c_28])).
% 8.57/3.08  tff(c_1080, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1072, c_157])).
% 8.57/3.08  tff(c_1086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_1080])).
% 8.57/3.08  tff(c_1087, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 8.57/3.08  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.57/3.08  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.57/3.08  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.57/3.08  tff(c_32, plain, (![A_33]: (k5_xboole_0(A_33, A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.57/3.08  tff(c_1271, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.57/3.08  tff(c_1297, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1271])).
% 8.57/3.08  tff(c_1328, plain, (![A_146]: (k4_xboole_0(A_146, A_146)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1297])).
% 8.57/3.08  tff(c_1333, plain, (![A_146]: (k4_xboole_0(A_146, k1_xboole_0)=k3_xboole_0(A_146, A_146))), inference(superposition, [status(thm), theory('equality')], [c_1328, c_20])).
% 8.57/3.08  tff(c_1337, plain, (![A_146]: (k4_xboole_0(A_146, k1_xboole_0)=A_146)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1333])).
% 8.57/3.08  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.57/3.08  tff(c_56, plain, (![A_43]: (~v1_xboole_0(k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.57/3.08  tff(c_1234, plain, (![B_136, A_137]: (r2_hidden(B_136, A_137) | ~m1_subset_1(B_136, A_137) | v1_xboole_0(A_137))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.57/3.08  tff(c_34, plain, (![C_38, A_34]: (r1_tarski(C_38, A_34) | ~r2_hidden(C_38, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.57/3.08  tff(c_1238, plain, (![B_136, A_34]: (r1_tarski(B_136, A_34) | ~m1_subset_1(B_136, k1_zfmisc_1(A_34)) | v1_xboole_0(k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_1234, c_34])).
% 8.57/3.08  tff(c_1242, plain, (![B_138, A_139]: (r1_tarski(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)))), inference(negUnitSimplification, [status(thm)], [c_56, c_1238])).
% 8.57/3.08  tff(c_1255, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1242])).
% 8.57/3.08  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.57/3.08  tff(c_1256, plain, (![A_140, B_141]: (k4_xboole_0(A_140, k4_xboole_0(A_140, B_141))=k3_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.57/3.08  tff(c_1265, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1256])).
% 8.57/3.08  tff(c_7946, plain, (![A_309, B_310]: (k3_xboole_0(A_309, k4_xboole_0(A_309, B_310))=k4_xboole_0(A_309, B_310))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1265])).
% 8.57/3.08  tff(c_1482, plain, (![A_151, C_152, B_153]: (r1_xboole_0(A_151, k4_xboole_0(C_152, B_153)) | ~r1_tarski(A_151, B_153))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.57/3.08  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.57/3.08  tff(c_1501, plain, (![A_151, C_152, B_153]: (k3_xboole_0(A_151, k4_xboole_0(C_152, B_153))=k1_xboole_0 | ~r1_tarski(A_151, B_153))), inference(resolution, [status(thm)], [c_1482, c_6])).
% 8.57/3.08  tff(c_8165, plain, (![A_311, B_312]: (k4_xboole_0(A_311, B_312)=k1_xboole_0 | ~r1_tarski(A_311, B_312))), inference(superposition, [status(thm), theory('equality')], [c_7946, c_1501])).
% 8.57/3.08  tff(c_8245, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1255, c_8165])).
% 8.57/3.08  tff(c_8318, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8245, c_20])).
% 8.57/3.08  tff(c_8344, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_8318])).
% 8.57/3.08  tff(c_1088, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_62])).
% 8.57/3.08  tff(c_2806, plain, (![A_206, B_207]: (k4_xboole_0(A_206, B_207)=k3_subset_1(A_206, B_207) | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.57/3.08  tff(c_2822, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_2806])).
% 8.57/3.08  tff(c_26, plain, (![B_25, A_24, C_26]: (r1_xboole_0(B_25, k4_xboole_0(A_24, C_26)) | ~r1_xboole_0(A_24, k4_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.57/3.08  tff(c_11568, plain, (![A_336]: (r1_xboole_0('#skF_3', k4_xboole_0(A_336, '#skF_5')) | ~r1_xboole_0(A_336, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2822, c_26])).
% 8.57/3.08  tff(c_11638, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1088, c_11568])).
% 8.57/3.08  tff(c_11652, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11638, c_6])).
% 8.57/3.08  tff(c_11718, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11652, c_18])).
% 8.57/3.08  tff(c_11749, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_11718])).
% 8.57/3.08  tff(c_105, plain, (![A_49, B_50]: (r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.57/3.08  tff(c_108, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 8.57/3.08  tff(c_1301, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1297])).
% 8.57/3.08  tff(c_1586, plain, (![A_156, A_157]: (r1_xboole_0(A_156, k1_xboole_0) | ~r1_tarski(A_156, A_157))), inference(superposition, [status(thm), theory('equality')], [c_1301, c_1482])).
% 8.57/3.08  tff(c_1603, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_108, c_1586])).
% 8.57/3.08  tff(c_1919, plain, (![B_177, A_178, C_179]: (r1_xboole_0(B_177, k4_xboole_0(A_178, C_179)) | ~r1_xboole_0(A_178, k4_xboole_0(B_177, C_179)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.57/3.08  tff(c_1934, plain, (![A_7, A_178]: (r1_xboole_0(A_7, k4_xboole_0(A_178, A_7)) | ~r1_xboole_0(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1301, c_1919])).
% 8.57/3.08  tff(c_1950, plain, (![A_180, A_181]: (r1_xboole_0(A_180, k4_xboole_0(A_181, A_180)))), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_1934])).
% 8.57/3.08  tff(c_2170, plain, (![A_188, A_189]: (k3_xboole_0(A_188, k4_xboole_0(A_189, A_188))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1950, c_6])).
% 8.57/3.08  tff(c_2187, plain, (![A_188, A_189]: (k4_xboole_0(A_188, k4_xboole_0(A_189, A_188))=k4_xboole_0(A_188, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2170, c_18])).
% 8.57/3.08  tff(c_2228, plain, (![A_188, A_189]: (k4_xboole_0(A_188, k4_xboole_0(A_189, A_188))=A_188)), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_2187])).
% 8.57/3.08  tff(c_1982, plain, (![A_180, A_181]: (k3_xboole_0(A_180, k4_xboole_0(A_181, A_180))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1950, c_6])).
% 8.57/3.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.57/3.08  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.57/3.08  tff(c_2918, plain, (![A_208, B_209, C_210]: (k5_xboole_0(k3_xboole_0(A_208, B_209), k3_xboole_0(C_210, B_209))=k3_xboole_0(k5_xboole_0(A_208, C_210), B_209))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.57/3.08  tff(c_2940, plain, (![A_208, B_209]: (k3_xboole_0(k5_xboole_0(A_208, k3_xboole_0(A_208, B_209)), B_209)=k4_xboole_0(k3_xboole_0(A_208, B_209), B_209))), inference(superposition, [status(thm), theory('equality')], [c_2918, c_12])).
% 8.57/3.08  tff(c_3042, plain, (![A_211, B_212]: (k4_xboole_0(k3_xboole_0(A_211, B_212), B_212)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_2, c_12, c_2940])).
% 8.57/3.08  tff(c_3058, plain, (![A_211, B_212, A_24]: (r1_xboole_0(k3_xboole_0(A_211, B_212), k4_xboole_0(A_24, B_212)) | ~r1_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3042, c_26])).
% 8.57/3.08  tff(c_4168, plain, (![A_236, B_237, A_238]: (r1_xboole_0(k3_xboole_0(A_236, B_237), k4_xboole_0(A_238, B_237)))), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_3058])).
% 8.57/3.08  tff(c_4216, plain, (![A_236, A_189, A_188]: (r1_xboole_0(k3_xboole_0(A_236, k4_xboole_0(A_189, A_188)), A_188))), inference(superposition, [status(thm), theory('equality')], [c_2228, c_4168])).
% 8.57/3.08  tff(c_13233, plain, (![A_367]: (r1_xboole_0(k3_xboole_0(A_367, '#skF_3'), k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11749, c_4216])).
% 8.57/3.08  tff(c_13248, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8344, c_13233])).
% 8.57/3.08  tff(c_13289, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_13248, c_6])).
% 8.57/3.08  tff(c_13372, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13289, c_12])).
% 8.57/3.08  tff(c_13409, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_13372])).
% 8.57/3.08  tff(c_1139, plain, (![B_120, A_121]: (k3_xboole_0(B_120, A_121)=k3_xboole_0(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.57/3.08  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.57/3.08  tff(c_1154, plain, (![B_120, A_121]: (r1_tarski(k3_xboole_0(B_120, A_121), A_121))), inference(superposition, [status(thm), theory('equality')], [c_1139, c_16])).
% 8.57/3.08  tff(c_13932, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13409, c_1154])).
% 8.57/3.08  tff(c_13958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1087, c_13932])).
% 8.57/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.08  
% 8.57/3.08  Inference rules
% 8.57/3.08  ----------------------
% 8.57/3.08  #Ref     : 0
% 8.57/3.08  #Sup     : 3566
% 8.57/3.08  #Fact    : 0
% 8.57/3.08  #Define  : 0
% 8.57/3.08  #Split   : 4
% 8.57/3.08  #Chain   : 0
% 8.57/3.08  #Close   : 0
% 8.57/3.08  
% 8.57/3.08  Ordering : KBO
% 8.57/3.08  
% 8.57/3.08  Simplification rules
% 8.57/3.08  ----------------------
% 8.57/3.08  #Subsume      : 83
% 8.57/3.08  #Demod        : 3048
% 8.57/3.08  #Tautology    : 2249
% 8.57/3.08  #SimpNegUnit  : 7
% 8.57/3.08  #BackRed      : 17
% 8.57/3.08  
% 8.57/3.08  #Partial instantiations: 0
% 8.57/3.08  #Strategies tried      : 1
% 8.57/3.08  
% 8.57/3.08  Timing (in seconds)
% 8.57/3.08  ----------------------
% 8.57/3.09  Preprocessing        : 0.33
% 8.57/3.09  Parsing              : 0.17
% 8.57/3.09  CNF conversion       : 0.02
% 8.57/3.09  Main loop            : 1.99
% 8.57/3.09  Inferencing          : 0.47
% 8.57/3.09  Reduction            : 0.98
% 8.57/3.09  Demodulation         : 0.82
% 8.57/3.09  BG Simplification    : 0.06
% 8.57/3.09  Subsumption          : 0.36
% 8.57/3.09  Abstraction          : 0.07
% 8.57/3.09  MUC search           : 0.00
% 8.57/3.09  Cooper               : 0.00
% 8.57/3.09  Total                : 2.37
% 8.57/3.09  Index Insertion      : 0.00
% 8.57/3.09  Index Deletion       : 0.00
% 8.57/3.09  Index Matching       : 0.00
% 8.57/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
