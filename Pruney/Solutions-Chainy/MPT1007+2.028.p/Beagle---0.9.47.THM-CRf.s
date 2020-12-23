%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 235 expanded)
%              Number of leaves         :   51 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 456 expanded)
%              Number of equality atoms :   56 ( 144 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_139,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_61] : ~ v1_xboole_0(k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_112,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_124,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_30,plain,(
    ! [A_27] :
      ( k2_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_124,c_30])).

tff(c_145,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_162,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_174,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_162])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = B_26
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_186,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_174,c_28])).

tff(c_189,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_186])).

tff(c_251,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(k7_relat_1(B_100,A_101)) = k9_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_260,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_251])).

tff(c_267,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_260])).

tff(c_20,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(A_18,k1_tarski(B_20)) = k11_relat_1(A_18,B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_305,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_20])).

tff(c_312,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_305])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,k1_relat_1(B_24))
      | k11_relat_1(B_24,A_23) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,(
    ! [C_94,B_95,A_96] :
      ( v5_relat_1(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_246,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_234])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_519,plain,(
    ! [B_144,C_145,A_146] :
      ( r2_hidden(k1_funct_1(B_144,C_145),A_146)
      | ~ r2_hidden(C_145,k1_relat_1(B_144))
      | ~ v1_funct_1(B_144)
      | ~ v5_relat_1(B_144,A_146)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_540,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_519,c_62])).

tff(c_548,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_246,c_70,c_540])).

tff(c_551,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_548])).

tff(c_557,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_312,c_551])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_557])).

tff(c_560,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_568,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_566,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_14])).

tff(c_60,plain,(
    ! [B_54,A_53,C_55] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_53,B_54,C_55) = A_53
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_977,plain,(
    ! [B_223,A_224,C_225] :
      ( B_223 = '#skF_6'
      | k1_relset_1(A_224,B_223,C_225) = A_224
      | ~ v1_funct_2(C_225,A_224,B_223)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_60])).

tff(c_993,plain,(
    ! [B_226,A_227] :
      ( B_226 = '#skF_6'
      | k1_relset_1(A_227,B_226,'#skF_6') = A_227
      | ~ v1_funct_2('#skF_6',A_227,B_226) ) ),
    inference(resolution,[status(thm)],[c_566,c_977])).

tff(c_1002,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_993])).

tff(c_1008,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_1002])).

tff(c_1083,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_2'(A_242,B_243,C_244),B_243)
      | k1_relset_1(B_243,A_242,C_244) = B_243
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(B_243,A_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1094,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_2'(A_242,B_243,'#skF_6'),B_243)
      | k1_relset_1(B_243,A_242,'#skF_6') = B_243 ) ),
    inference(resolution,[status(thm)],[c_566,c_1083])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_567,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_2])).

tff(c_1230,plain,(
    ! [D_258,A_259,B_260,C_261] :
      ( r2_hidden(k4_tarski(D_258,'#skF_3'(A_259,B_260,C_261,D_258)),C_261)
      | ~ r2_hidden(D_258,B_260)
      | k1_relset_1(B_260,A_259,C_261) != B_260
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(B_260,A_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    ! [B_33,A_32] :
      ( ~ r1_tarski(B_33,A_32)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1538,plain,(
    ! [C_305,D_306,A_307,B_308] :
      ( ~ r1_tarski(C_305,k4_tarski(D_306,'#skF_3'(A_307,B_308,C_305,D_306)))
      | ~ r2_hidden(D_306,B_308)
      | k1_relset_1(B_308,A_307,C_305) != B_308
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(B_308,A_307))) ) ),
    inference(resolution,[status(thm)],[c_1230,c_36])).

tff(c_1542,plain,(
    ! [D_306,B_308,A_307] :
      ( ~ r2_hidden(D_306,B_308)
      | k1_relset_1(B_308,A_307,'#skF_6') != B_308
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_308,A_307))) ) ),
    inference(resolution,[status(thm)],[c_567,c_1538])).

tff(c_1546,plain,(
    ! [D_309,B_310,A_311] :
      ( ~ r2_hidden(D_309,B_310)
      | k1_relset_1(B_310,A_311,'#skF_6') != B_310 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_1542])).

tff(c_1565,plain,(
    ! [B_312,A_313,A_314] :
      ( k1_relset_1(B_312,A_313,'#skF_6') != B_312
      | k1_relset_1(B_312,A_314,'#skF_6') = B_312 ) ),
    inference(resolution,[status(thm)],[c_1094,c_1546])).

tff(c_1579,plain,(
    ! [A_314] : k1_relset_1(k1_tarski('#skF_4'),A_314,'#skF_6') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1565])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1592,plain,(
    ! [B_316,A_317,A_318] :
      ( k1_relset_1(B_316,A_317,'#skF_6') != B_316
      | v1_xboole_0(B_316)
      | ~ m1_subset_1(A_318,B_316) ) ),
    inference(resolution,[status(thm)],[c_16,c_1546])).

tff(c_1594,plain,(
    ! [A_318] :
      ( v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_318,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1579,c_1592])).

tff(c_1609,plain,(
    ! [A_319] : ~ m1_subset_1(A_319,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1594])).

tff(c_1624,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_1609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:27:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.69  
% 4.26/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.26/1.70  
% 4.26/1.70  %Foreground sorts:
% 4.26/1.70  
% 4.26/1.70  
% 4.26/1.70  %Background operators:
% 4.26/1.70  
% 4.26/1.70  
% 4.26/1.70  %Foreground operators:
% 4.26/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.26/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.26/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.26/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.26/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.26/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.26/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.26/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.26/1.70  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.26/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.26/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.26/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.26/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.26/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.26/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.26/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.26/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.26/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.26/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.26/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.70  
% 4.26/1.72  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.26/1.72  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.26/1.72  tff(f_36, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 4.26/1.72  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.26/1.72  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.72  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.26/1.72  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.26/1.72  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.26/1.72  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.26/1.72  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.26/1.72  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.26/1.72  tff(f_94, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 4.26/1.72  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.26/1.72  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.26/1.72  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 4.26/1.72  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.26/1.72  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.26/1.72  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.26/1.72  tff(c_12, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.26/1.72  tff(c_77, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.72  tff(c_10, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.26/1.72  tff(c_82, plain, (![A_61]: (~v1_xboole_0(k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 4.26/1.72  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.26/1.72  tff(c_112, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.26/1.72  tff(c_124, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_112])).
% 4.26/1.72  tff(c_30, plain, (![A_27]: (k2_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.26/1.72  tff(c_133, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_124, c_30])).
% 4.26/1.72  tff(c_145, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_133])).
% 4.26/1.72  tff(c_162, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.26/1.72  tff(c_174, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_162])).
% 4.26/1.72  tff(c_28, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=B_26 | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.26/1.72  tff(c_186, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_174, c_28])).
% 4.26/1.72  tff(c_189, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_186])).
% 4.26/1.72  tff(c_251, plain, (![B_100, A_101]: (k2_relat_1(k7_relat_1(B_100, A_101))=k9_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.26/1.72  tff(c_260, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_189, c_251])).
% 4.26/1.72  tff(c_267, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_260])).
% 4.26/1.72  tff(c_20, plain, (![A_18, B_20]: (k9_relat_1(A_18, k1_tarski(B_20))=k11_relat_1(A_18, B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.26/1.72  tff(c_305, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_267, c_20])).
% 4.26/1.72  tff(c_312, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_305])).
% 4.26/1.72  tff(c_24, plain, (![A_23, B_24]: (r2_hidden(A_23, k1_relat_1(B_24)) | k11_relat_1(B_24, A_23)=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.26/1.72  tff(c_234, plain, (![C_94, B_95, A_96]: (v5_relat_1(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.26/1.72  tff(c_246, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_234])).
% 4.26/1.72  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.26/1.72  tff(c_519, plain, (![B_144, C_145, A_146]: (r2_hidden(k1_funct_1(B_144, C_145), A_146) | ~r2_hidden(C_145, k1_relat_1(B_144)) | ~v1_funct_1(B_144) | ~v5_relat_1(B_144, A_146) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.26/1.72  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.26/1.72  tff(c_540, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_519, c_62])).
% 4.26/1.72  tff(c_548, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_246, c_70, c_540])).
% 4.26/1.72  tff(c_551, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_548])).
% 4.26/1.72  tff(c_557, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_312, c_551])).
% 4.26/1.72  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_557])).
% 4.26/1.72  tff(c_560, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_133])).
% 4.26/1.72  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.26/1.72  tff(c_568, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_64])).
% 4.26/1.72  tff(c_68, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.26/1.72  tff(c_14, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.72  tff(c_566, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_14])).
% 4.26/1.72  tff(c_60, plain, (![B_54, A_53, C_55]: (k1_xboole_0=B_54 | k1_relset_1(A_53, B_54, C_55)=A_53 | ~v1_funct_2(C_55, A_53, B_54) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.26/1.72  tff(c_977, plain, (![B_223, A_224, C_225]: (B_223='#skF_6' | k1_relset_1(A_224, B_223, C_225)=A_224 | ~v1_funct_2(C_225, A_224, B_223) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_60])).
% 4.26/1.72  tff(c_993, plain, (![B_226, A_227]: (B_226='#skF_6' | k1_relset_1(A_227, B_226, '#skF_6')=A_227 | ~v1_funct_2('#skF_6', A_227, B_226))), inference(resolution, [status(thm)], [c_566, c_977])).
% 4.26/1.72  tff(c_1002, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_68, c_993])).
% 4.26/1.72  tff(c_1008, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_568, c_1002])).
% 4.26/1.72  tff(c_1083, plain, (![A_242, B_243, C_244]: (r2_hidden('#skF_2'(A_242, B_243, C_244), B_243) | k1_relset_1(B_243, A_242, C_244)=B_243 | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(B_243, A_242))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.26/1.72  tff(c_1094, plain, (![A_242, B_243]: (r2_hidden('#skF_2'(A_242, B_243, '#skF_6'), B_243) | k1_relset_1(B_243, A_242, '#skF_6')=B_243)), inference(resolution, [status(thm)], [c_566, c_1083])).
% 4.26/1.72  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.26/1.72  tff(c_567, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_2])).
% 4.26/1.72  tff(c_1230, plain, (![D_258, A_259, B_260, C_261]: (r2_hidden(k4_tarski(D_258, '#skF_3'(A_259, B_260, C_261, D_258)), C_261) | ~r2_hidden(D_258, B_260) | k1_relset_1(B_260, A_259, C_261)!=B_260 | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(B_260, A_259))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.26/1.72  tff(c_36, plain, (![B_33, A_32]: (~r1_tarski(B_33, A_32) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.26/1.72  tff(c_1538, plain, (![C_305, D_306, A_307, B_308]: (~r1_tarski(C_305, k4_tarski(D_306, '#skF_3'(A_307, B_308, C_305, D_306))) | ~r2_hidden(D_306, B_308) | k1_relset_1(B_308, A_307, C_305)!=B_308 | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(B_308, A_307))))), inference(resolution, [status(thm)], [c_1230, c_36])).
% 4.26/1.72  tff(c_1542, plain, (![D_306, B_308, A_307]: (~r2_hidden(D_306, B_308) | k1_relset_1(B_308, A_307, '#skF_6')!=B_308 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_308, A_307))))), inference(resolution, [status(thm)], [c_567, c_1538])).
% 4.26/1.72  tff(c_1546, plain, (![D_309, B_310, A_311]: (~r2_hidden(D_309, B_310) | k1_relset_1(B_310, A_311, '#skF_6')!=B_310)), inference(demodulation, [status(thm), theory('equality')], [c_566, c_1542])).
% 4.26/1.72  tff(c_1565, plain, (![B_312, A_313, A_314]: (k1_relset_1(B_312, A_313, '#skF_6')!=B_312 | k1_relset_1(B_312, A_314, '#skF_6')=B_312)), inference(resolution, [status(thm)], [c_1094, c_1546])).
% 4.26/1.72  tff(c_1579, plain, (![A_314]: (k1_relset_1(k1_tarski('#skF_4'), A_314, '#skF_6')=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1565])).
% 4.26/1.72  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.26/1.72  tff(c_1592, plain, (![B_316, A_317, A_318]: (k1_relset_1(B_316, A_317, '#skF_6')!=B_316 | v1_xboole_0(B_316) | ~m1_subset_1(A_318, B_316))), inference(resolution, [status(thm)], [c_16, c_1546])).
% 4.26/1.72  tff(c_1594, plain, (![A_318]: (v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_318, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1579, c_1592])).
% 4.26/1.72  tff(c_1609, plain, (![A_319]: (~m1_subset_1(A_319, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_82, c_1594])).
% 4.26/1.72  tff(c_1624, plain, $false, inference(resolution, [status(thm)], [c_12, c_1609])).
% 4.26/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.72  
% 4.26/1.72  Inference rules
% 4.26/1.72  ----------------------
% 4.26/1.72  #Ref     : 0
% 4.26/1.72  #Sup     : 306
% 4.26/1.72  #Fact    : 0
% 4.26/1.72  #Define  : 0
% 4.26/1.72  #Split   : 6
% 4.26/1.72  #Chain   : 0
% 4.26/1.72  #Close   : 0
% 4.26/1.72  
% 4.26/1.72  Ordering : KBO
% 4.26/1.72  
% 4.26/1.72  Simplification rules
% 4.26/1.72  ----------------------
% 4.26/1.72  #Subsume      : 11
% 4.26/1.72  #Demod        : 105
% 4.26/1.72  #Tautology    : 107
% 4.26/1.72  #SimpNegUnit  : 3
% 4.26/1.72  #BackRed      : 8
% 4.26/1.72  
% 4.26/1.72  #Partial instantiations: 0
% 4.26/1.72  #Strategies tried      : 1
% 4.26/1.72  
% 4.26/1.72  Timing (in seconds)
% 4.26/1.72  ----------------------
% 4.26/1.72  Preprocessing        : 0.35
% 4.26/1.72  Parsing              : 0.18
% 4.26/1.72  CNF conversion       : 0.02
% 4.26/1.72  Main loop            : 0.61
% 4.26/1.72  Inferencing          : 0.23
% 4.26/1.72  Reduction            : 0.18
% 4.26/1.72  Demodulation         : 0.13
% 4.26/1.72  BG Simplification    : 0.03
% 4.26/1.72  Subsumption          : 0.10
% 4.26/1.72  Abstraction          : 0.03
% 4.26/1.72  MUC search           : 0.00
% 4.26/1.72  Cooper               : 0.00
% 4.26/1.72  Total                : 1.00
% 4.26/1.72  Index Insertion      : 0.00
% 4.26/1.72  Index Deletion       : 0.00
% 4.26/1.72  Index Matching       : 0.00
% 4.26/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
