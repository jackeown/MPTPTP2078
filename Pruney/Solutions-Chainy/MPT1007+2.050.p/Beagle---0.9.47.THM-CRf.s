%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 181 expanded)
%              Number of leaves         :   48 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 388 expanded)
%              Number of equality atoms :   42 (  98 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_493,plain,(
    ! [A_152,B_153,C_154] :
      ( r2_hidden('#skF_4'(A_152,B_153,C_154),B_153)
      | k1_relset_1(B_153,A_152,C_154) = B_153
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(B_153,A_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_506,plain,
    ( r2_hidden('#skF_4'('#skF_7',k1_tarski('#skF_6'),'#skF_8'),k1_tarski('#skF_6'))
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_493])).

tff(c_623,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_109,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_97])).

tff(c_212,plain,(
    ! [A_109] :
      ( k1_xboole_0 = A_109
      | r2_hidden(k4_tarski('#skF_2'(A_109),'#skF_3'(A_109)),A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_918,plain,(
    ! [A_208,A_209] :
      ( r2_hidden(k4_tarski('#skF_2'(A_208),'#skF_3'(A_208)),A_209)
      | ~ m1_subset_1(A_208,k1_zfmisc_1(A_209))
      | k1_xboole_0 = A_208
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_212,c_20])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_956,plain,(
    ! [C_210,A_211,D_212] :
      ( C_210 = '#skF_2'(A_211)
      | ~ m1_subset_1(A_211,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_210),D_212)))
      | k1_xboole_0 = A_211
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_918,c_16])).

tff(c_967,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_956])).

tff(c_980,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_967])).

tff(c_988,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1018,plain,(
    ! [A_19] : m1_subset_1('#skF_8',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_22])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1019,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_2])).

tff(c_873,plain,(
    ! [D_204,A_205,B_206,C_207] :
      ( r2_hidden(k4_tarski(D_204,'#skF_5'(A_205,B_206,C_207,D_204)),C_207)
      | ~ r2_hidden(D_204,B_206)
      | k1_relset_1(B_206,A_205,C_207) != B_206
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(B_206,A_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(B_36,A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5724,plain,(
    ! [C_6001,D_6002,A_6003,B_6004] :
      ( ~ r1_tarski(C_6001,k4_tarski(D_6002,'#skF_5'(A_6003,B_6004,C_6001,D_6002)))
      | ~ r2_hidden(D_6002,B_6004)
      | k1_relset_1(B_6004,A_6003,C_6001) != B_6004
      | ~ m1_subset_1(C_6001,k1_zfmisc_1(k2_zfmisc_1(B_6004,A_6003))) ) ),
    inference(resolution,[status(thm)],[c_873,c_36])).

tff(c_5737,plain,(
    ! [D_6002,B_6004,A_6003] :
      ( ~ r2_hidden(D_6002,B_6004)
      | k1_relset_1(B_6004,A_6003,'#skF_8') != B_6004
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_6004,A_6003))) ) ),
    inference(resolution,[status(thm)],[c_1019,c_5724])).

tff(c_5743,plain,(
    ! [D_6037,B_6038,A_6039] :
      ( ~ r2_hidden(D_6037,B_6038)
      | k1_relset_1(B_6038,A_6039,'#skF_8') != B_6038 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_5737])).

tff(c_5857,plain,(
    ! [B_6044,A_6045,A_6046] :
      ( k1_relset_1(B_6044,A_6045,'#skF_8') != B_6044
      | v1_xboole_0(B_6044)
      | ~ m1_subset_1(A_6046,B_6044) ) ),
    inference(resolution,[status(thm)],[c_24,c_5743])).

tff(c_5867,plain,(
    ! [A_6046] :
      ( v1_xboole_0(k1_tarski('#skF_6'))
      | ~ m1_subset_1(A_6046,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_5857])).

tff(c_5877,plain,(
    ! [A_6047] : ~ m1_subset_1(A_6047,k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_5867])).

tff(c_5909,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_5877])).

tff(c_5911,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_151,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_163,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_151])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_465,plain,(
    ! [B_149,C_150,A_151] :
      ( r2_hidden(k1_funct_1(B_149,C_150),A_151)
      | ~ r2_hidden(C_150,k1_relat_1(B_149))
      | ~ v1_funct_1(B_149)
      | ~ v5_relat_1(B_149,A_151)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_480,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_465,c_62])).

tff(c_487,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_163,c_70,c_480])).

tff(c_5910,plain,(
    '#skF_2'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_32,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | r2_hidden(k4_tarski('#skF_2'(A_28),'#skF_3'(A_28)),A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_264,plain,(
    ! [A_117,C_118,B_119] :
      ( r2_hidden(A_117,k1_relat_1(C_118))
      | ~ r2_hidden(k4_tarski(A_117,B_119),C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_276,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_2'(A_28),k1_relat_1(A_28))
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_32,c_264])).

tff(c_5925,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5910,c_276])).

tff(c_5941,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_5925])).

tff(c_5943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5911,c_487,c_5941])).

tff(c_5945,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') != k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_5972,plain,(
    ! [B_6053,A_6054,C_6055] :
      ( k1_xboole_0 = B_6053
      | k1_relset_1(A_6054,B_6053,C_6055) = A_6054
      | ~ v1_funct_2(C_6055,A_6054,B_6053)
      | ~ m1_subset_1(C_6055,k1_zfmisc_1(k2_zfmisc_1(A_6054,B_6053))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5979,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_5972])).

tff(c_5991,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5979])).

tff(c_5993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5945,c_64,c_5991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.53  
% 7.41/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3
% 7.41/2.53  
% 7.41/2.53  %Foreground sorts:
% 7.41/2.53  
% 7.41/2.53  
% 7.41/2.53  %Background operators:
% 7.41/2.53  
% 7.41/2.53  
% 7.41/2.53  %Foreground operators:
% 7.41/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.41/2.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.41/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.41/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.41/2.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.41/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.41/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.41/2.53  tff('#skF_7', type, '#skF_7': $i).
% 7.41/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.41/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.41/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.41/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.41/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.41/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.41/2.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.41/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.41/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.41/2.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.41/2.53  tff('#skF_8', type, '#skF_8': $i).
% 7.41/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.41/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.41/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.41/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.41/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.41/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.41/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.41/2.53  
% 7.41/2.55  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.41/2.55  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.41/2.55  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 7.41/2.55  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.41/2.55  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.41/2.55  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.41/2.55  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 7.41/2.55  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.41/2.55  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 7.41/2.55  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.41/2.55  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.41/2.55  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.41/2.55  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.41/2.55  tff(f_93, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 7.41/2.55  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 7.41/2.55  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.41/2.55  tff(c_18, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.55  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.41/2.55  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.41/2.55  tff(c_493, plain, (![A_152, B_153, C_154]: (r2_hidden('#skF_4'(A_152, B_153, C_154), B_153) | k1_relset_1(B_153, A_152, C_154)=B_153 | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(B_153, A_152))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.41/2.55  tff(c_506, plain, (r2_hidden('#skF_4'('#skF_7', k1_tarski('#skF_6'), '#skF_8'), k1_tarski('#skF_6')) | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_66, c_493])).
% 7.41/2.55  tff(c_623, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_506])).
% 7.41/2.55  tff(c_24, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.41/2.55  tff(c_97, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.41/2.55  tff(c_109, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_97])).
% 7.41/2.55  tff(c_212, plain, (![A_109]: (k1_xboole_0=A_109 | r2_hidden(k4_tarski('#skF_2'(A_109), '#skF_3'(A_109)), A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.41/2.55  tff(c_20, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.41/2.55  tff(c_918, plain, (![A_208, A_209]: (r2_hidden(k4_tarski('#skF_2'(A_208), '#skF_3'(A_208)), A_209) | ~m1_subset_1(A_208, k1_zfmisc_1(A_209)) | k1_xboole_0=A_208 | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_212, c_20])).
% 7.41/2.55  tff(c_16, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.41/2.55  tff(c_956, plain, (![C_210, A_211, D_212]: (C_210='#skF_2'(A_211) | ~m1_subset_1(A_211, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_210), D_212))) | k1_xboole_0=A_211 | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_918, c_16])).
% 7.41/2.55  tff(c_967, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_956])).
% 7.41/2.55  tff(c_980, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_967])).
% 7.41/2.55  tff(c_988, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_980])).
% 7.41/2.55  tff(c_22, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.41/2.55  tff(c_1018, plain, (![A_19]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_22])).
% 7.41/2.55  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.55  tff(c_1019, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_2])).
% 7.41/2.55  tff(c_873, plain, (![D_204, A_205, B_206, C_207]: (r2_hidden(k4_tarski(D_204, '#skF_5'(A_205, B_206, C_207, D_204)), C_207) | ~r2_hidden(D_204, B_206) | k1_relset_1(B_206, A_205, C_207)!=B_206 | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(B_206, A_205))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.41/2.55  tff(c_36, plain, (![B_36, A_35]: (~r1_tarski(B_36, A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.41/2.55  tff(c_5724, plain, (![C_6001, D_6002, A_6003, B_6004]: (~r1_tarski(C_6001, k4_tarski(D_6002, '#skF_5'(A_6003, B_6004, C_6001, D_6002))) | ~r2_hidden(D_6002, B_6004) | k1_relset_1(B_6004, A_6003, C_6001)!=B_6004 | ~m1_subset_1(C_6001, k1_zfmisc_1(k2_zfmisc_1(B_6004, A_6003))))), inference(resolution, [status(thm)], [c_873, c_36])).
% 7.41/2.55  tff(c_5737, plain, (![D_6002, B_6004, A_6003]: (~r2_hidden(D_6002, B_6004) | k1_relset_1(B_6004, A_6003, '#skF_8')!=B_6004 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_6004, A_6003))))), inference(resolution, [status(thm)], [c_1019, c_5724])).
% 7.41/2.55  tff(c_5743, plain, (![D_6037, B_6038, A_6039]: (~r2_hidden(D_6037, B_6038) | k1_relset_1(B_6038, A_6039, '#skF_8')!=B_6038)), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_5737])).
% 7.41/2.55  tff(c_5857, plain, (![B_6044, A_6045, A_6046]: (k1_relset_1(B_6044, A_6045, '#skF_8')!=B_6044 | v1_xboole_0(B_6044) | ~m1_subset_1(A_6046, B_6044))), inference(resolution, [status(thm)], [c_24, c_5743])).
% 7.41/2.55  tff(c_5867, plain, (![A_6046]: (v1_xboole_0(k1_tarski('#skF_6')) | ~m1_subset_1(A_6046, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_623, c_5857])).
% 7.41/2.55  tff(c_5877, plain, (![A_6047]: (~m1_subset_1(A_6047, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_10, c_5867])).
% 7.41/2.55  tff(c_5909, plain, $false, inference(resolution, [status(thm)], [c_18, c_5877])).
% 7.41/2.55  tff(c_5911, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_980])).
% 7.41/2.55  tff(c_151, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.41/2.55  tff(c_163, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_66, c_151])).
% 7.41/2.55  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.41/2.55  tff(c_465, plain, (![B_149, C_150, A_151]: (r2_hidden(k1_funct_1(B_149, C_150), A_151) | ~r2_hidden(C_150, k1_relat_1(B_149)) | ~v1_funct_1(B_149) | ~v5_relat_1(B_149, A_151) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.41/2.55  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.41/2.55  tff(c_480, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_465, c_62])).
% 7.41/2.55  tff(c_487, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_163, c_70, c_480])).
% 7.41/2.55  tff(c_5910, plain, ('#skF_2'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_980])).
% 7.41/2.55  tff(c_32, plain, (![A_28]: (k1_xboole_0=A_28 | r2_hidden(k4_tarski('#skF_2'(A_28), '#skF_3'(A_28)), A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.41/2.55  tff(c_264, plain, (![A_117, C_118, B_119]: (r2_hidden(A_117, k1_relat_1(C_118)) | ~r2_hidden(k4_tarski(A_117, B_119), C_118) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.41/2.55  tff(c_276, plain, (![A_28]: (r2_hidden('#skF_2'(A_28), k1_relat_1(A_28)) | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_32, c_264])).
% 7.41/2.55  tff(c_5925, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5910, c_276])).
% 7.41/2.55  tff(c_5941, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_5925])).
% 7.41/2.55  tff(c_5943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5911, c_487, c_5941])).
% 7.41/2.55  tff(c_5945, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')!=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_506])).
% 7.41/2.55  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.41/2.55  tff(c_68, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.41/2.55  tff(c_5972, plain, (![B_6053, A_6054, C_6055]: (k1_xboole_0=B_6053 | k1_relset_1(A_6054, B_6053, C_6055)=A_6054 | ~v1_funct_2(C_6055, A_6054, B_6053) | ~m1_subset_1(C_6055, k1_zfmisc_1(k2_zfmisc_1(A_6054, B_6053))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.41/2.55  tff(c_5979, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_66, c_5972])).
% 7.41/2.55  tff(c_5991, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5979])).
% 7.41/2.55  tff(c_5993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5945, c_64, c_5991])).
% 7.41/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.55  
% 7.41/2.55  Inference rules
% 7.41/2.55  ----------------------
% 7.41/2.55  #Ref     : 0
% 7.41/2.55  #Sup     : 1384
% 7.41/2.55  #Fact    : 0
% 7.41/2.55  #Define  : 0
% 7.41/2.55  #Split   : 19
% 7.41/2.55  #Chain   : 0
% 7.41/2.55  #Close   : 0
% 7.41/2.55  
% 7.41/2.55  Ordering : KBO
% 7.41/2.55  
% 7.41/2.55  Simplification rules
% 7.41/2.55  ----------------------
% 7.41/2.55  #Subsume      : 144
% 7.41/2.55  #Demod        : 301
% 7.41/2.55  #Tautology    : 150
% 7.41/2.55  #SimpNegUnit  : 11
% 7.41/2.55  #BackRed      : 33
% 7.41/2.55  
% 7.41/2.55  #Partial instantiations: 3440
% 7.41/2.55  #Strategies tried      : 1
% 7.41/2.55  
% 7.41/2.55  Timing (in seconds)
% 7.41/2.55  ----------------------
% 7.41/2.55  Preprocessing        : 0.34
% 7.41/2.55  Parsing              : 0.17
% 7.41/2.55  CNF conversion       : 0.02
% 7.41/2.55  Main loop            : 1.40
% 7.41/2.55  Inferencing          : 0.48
% 7.41/2.55  Reduction            : 0.41
% 7.41/2.55  Demodulation         : 0.28
% 7.41/2.55  BG Simplification    : 0.06
% 7.41/2.55  Subsumption          : 0.33
% 7.41/2.55  Abstraction          : 0.07
% 7.41/2.55  MUC search           : 0.00
% 7.41/2.55  Cooper               : 0.00
% 7.41/2.55  Total                : 1.77
% 7.41/2.55  Index Insertion      : 0.00
% 7.41/2.55  Index Deletion       : 0.00
% 7.41/2.55  Index Matching       : 0.00
% 7.41/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
