%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 378 expanded)
%              Number of leaves         :   41 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 830 expanded)
%              Number of equality atoms :   39 ( 180 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_138,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_147,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_141])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1329,plain,(
    ! [B_185,A_186] :
      ( k1_tarski(k1_funct_1(B_185,A_186)) = k2_relat_1(B_185)
      | k1_tarski(A_186) != k1_relat_1(B_185)
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1338,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_60])).

tff(c_1344,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_68,c_1338])).

tff(c_1392,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1344])).

tff(c_270,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_284,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_270])).

tff(c_332,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1839,plain,(
    ! [B_249,B_250] :
      ( k1_tarski(B_249) = k1_relat_1(B_250)
      | k1_relat_1(B_250) = k1_xboole_0
      | ~ v4_relat_1(B_250,k1_tarski(B_249))
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_332,c_16])).

tff(c_1869,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_284,c_1839])).

tff(c_1882,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1869])).

tff(c_1883,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1392,c_1882])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35),A_34)))
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1903,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_34)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_34)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_54])).

tff(c_1935,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_68,c_26,c_1903])).

tff(c_1990,plain,(
    ! [A_253] : ~ r1_tarski(k2_relat_1('#skF_4'),A_253) ),
    inference(splitLeft,[status(thm)],[c_1935])).

tff(c_1995,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1990])).

tff(c_1996,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1935])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2019,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1996,c_28])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_165])).

tff(c_2053,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2019,c_177])).

tff(c_2098,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_8])).

tff(c_83,plain,(
    ! [A_40] : k2_zfmisc_1(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_202,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k9_relat_1(B_58,A_59),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_210,plain,(
    ! [A_59] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_59),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_202])).

tff(c_224,plain,(
    ! [A_63] : r1_tarski(k9_relat_1(k1_xboole_0,A_63),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_210])).

tff(c_233,plain,(
    ! [A_63] : k9_relat_1(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_224,c_177])).

tff(c_2092,plain,(
    ! [A_63] : k9_relat_1('#skF_4',A_63) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2053,c_233])).

tff(c_1426,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_relset_1(A_195,B_196,C_197,D_198) = k9_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1436,plain,(
    ! [D_198] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_198) = k9_relat_1('#skF_4',D_198) ),
    inference(resolution,[status(thm)],[c_64,c_1426])).

tff(c_1438,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_60])).

tff(c_2343,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_1438])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_2343])).

tff(c_2349,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1344])).

tff(c_2354,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_64])).

tff(c_52,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k7_relset_1(A_30,B_31,C_32,D_33) = k9_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2406,plain,(
    ! [D_33] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_33) = k9_relat_1('#skF_4',D_33) ),
    inference(resolution,[status(thm)],[c_2354,c_52])).

tff(c_2348,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1344])).

tff(c_2416,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_2348])).

tff(c_2435,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2416])).

tff(c_2447,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2435])).

tff(c_2451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.91  
% 4.32/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.67/1.91  
% 4.67/1.91  %Foreground sorts:
% 4.67/1.91  
% 4.67/1.91  
% 4.67/1.91  %Background operators:
% 4.67/1.91  
% 4.67/1.91  
% 4.67/1.91  %Foreground operators:
% 4.67/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.67/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.67/1.91  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.67/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.67/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.67/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.67/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.67/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.67/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.67/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.67/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.67/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.91  
% 4.67/1.93  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.67/1.93  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.67/1.93  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.67/1.93  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.67/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.67/1.93  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.67/1.93  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.67/1.93  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.67/1.93  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.67/1.93  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.67/1.93  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.67/1.93  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.67/1.93  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.67/1.93  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.67/1.93  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.67/1.93  tff(c_38, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.67/1.93  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.67/1.93  tff(c_138, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.67/1.93  tff(c_141, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_138])).
% 4.67/1.93  tff(c_147, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_141])).
% 4.67/1.93  tff(c_40, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.67/1.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.93  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.67/1.93  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.67/1.93  tff(c_1329, plain, (![B_185, A_186]: (k1_tarski(k1_funct_1(B_185, A_186))=k2_relat_1(B_185) | k1_tarski(A_186)!=k1_relat_1(B_185) | ~v1_funct_1(B_185) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.67/1.93  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.67/1.93  tff(c_1338, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1329, c_60])).
% 4.67/1.93  tff(c_1344, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_68, c_1338])).
% 4.67/1.93  tff(c_1392, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1344])).
% 4.67/1.93  tff(c_270, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.67/1.93  tff(c_284, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_270])).
% 4.67/1.93  tff(c_332, plain, (![B_85, A_86]: (r1_tarski(k1_relat_1(B_85), A_86) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.67/1.93  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.67/1.93  tff(c_1839, plain, (![B_249, B_250]: (k1_tarski(B_249)=k1_relat_1(B_250) | k1_relat_1(B_250)=k1_xboole_0 | ~v4_relat_1(B_250, k1_tarski(B_249)) | ~v1_relat_1(B_250))), inference(resolution, [status(thm)], [c_332, c_16])).
% 4.67/1.93  tff(c_1869, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_284, c_1839])).
% 4.67/1.93  tff(c_1882, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1869])).
% 4.67/1.93  tff(c_1883, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1392, c_1882])).
% 4.67/1.93  tff(c_54, plain, (![B_35, A_34]: (m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35), A_34))) | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.67/1.93  tff(c_1903, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_34))) | ~r1_tarski(k2_relat_1('#skF_4'), A_34) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1883, c_54])).
% 4.67/1.93  tff(c_1935, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_68, c_26, c_1903])).
% 4.67/1.93  tff(c_1990, plain, (![A_253]: (~r1_tarski(k2_relat_1('#skF_4'), A_253))), inference(splitLeft, [status(thm)], [c_1935])).
% 4.67/1.93  tff(c_1995, plain, $false, inference(resolution, [status(thm)], [c_6, c_1990])).
% 4.67/1.93  tff(c_1996, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1935])).
% 4.67/1.93  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.93  tff(c_2019, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1996, c_28])).
% 4.67/1.93  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.93  tff(c_165, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.93  tff(c_177, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_165])).
% 4.67/1.93  tff(c_2053, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2019, c_177])).
% 4.67/1.93  tff(c_2098, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_8])).
% 4.67/1.93  tff(c_83, plain, (![A_40]: (k2_zfmisc_1(A_40, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.67/1.93  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_38])).
% 4.67/1.93  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.67/1.93  tff(c_202, plain, (![B_58, A_59]: (r1_tarski(k9_relat_1(B_58, A_59), k2_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.67/1.93  tff(c_210, plain, (![A_59]: (r1_tarski(k9_relat_1(k1_xboole_0, A_59), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_202])).
% 4.67/1.93  tff(c_224, plain, (![A_63]: (r1_tarski(k9_relat_1(k1_xboole_0, A_63), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_210])).
% 4.67/1.93  tff(c_233, plain, (![A_63]: (k9_relat_1(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_224, c_177])).
% 4.67/1.93  tff(c_2092, plain, (![A_63]: (k9_relat_1('#skF_4', A_63)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2053, c_233])).
% 4.67/1.93  tff(c_1426, plain, (![A_195, B_196, C_197, D_198]: (k7_relset_1(A_195, B_196, C_197, D_198)=k9_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.93  tff(c_1436, plain, (![D_198]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_198)=k9_relat_1('#skF_4', D_198))), inference(resolution, [status(thm)], [c_64, c_1426])).
% 4.67/1.93  tff(c_1438, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_60])).
% 4.67/1.93  tff(c_2343, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_1438])).
% 4.67/1.93  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2098, c_2343])).
% 4.67/1.93  tff(c_2349, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1344])).
% 4.67/1.93  tff(c_2354, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_64])).
% 4.67/1.93  tff(c_52, plain, (![A_30, B_31, C_32, D_33]: (k7_relset_1(A_30, B_31, C_32, D_33)=k9_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.93  tff(c_2406, plain, (![D_33]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_33)=k9_relat_1('#skF_4', D_33))), inference(resolution, [status(thm)], [c_2354, c_52])).
% 4.67/1.93  tff(c_2348, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1344])).
% 4.67/1.93  tff(c_2416, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_2348])).
% 4.67/1.93  tff(c_2435, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2416])).
% 4.67/1.93  tff(c_2447, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2435])).
% 4.67/1.93  tff(c_2451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_2447])).
% 4.67/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.93  
% 4.67/1.93  Inference rules
% 4.67/1.93  ----------------------
% 4.67/1.93  #Ref     : 0
% 4.67/1.93  #Sup     : 485
% 4.67/1.93  #Fact    : 0
% 4.67/1.93  #Define  : 0
% 4.67/1.93  #Split   : 10
% 4.67/1.93  #Chain   : 0
% 4.67/1.93  #Close   : 0
% 4.67/1.93  
% 4.67/1.93  Ordering : KBO
% 4.67/1.93  
% 4.67/1.93  Simplification rules
% 4.67/1.93  ----------------------
% 4.67/1.93  #Subsume      : 66
% 4.67/1.93  #Demod        : 630
% 4.67/1.93  #Tautology    : 256
% 4.67/1.93  #SimpNegUnit  : 18
% 4.67/1.93  #BackRed      : 108
% 4.67/1.93  
% 4.67/1.93  #Partial instantiations: 0
% 4.67/1.93  #Strategies tried      : 1
% 4.67/1.93  
% 4.67/1.93  Timing (in seconds)
% 4.67/1.93  ----------------------
% 4.67/1.93  Preprocessing        : 0.36
% 4.67/1.93  Parsing              : 0.19
% 4.67/1.93  CNF conversion       : 0.02
% 4.67/1.93  Main loop            : 0.75
% 4.67/1.93  Inferencing          : 0.27
% 4.67/1.93  Reduction            : 0.25
% 4.67/1.93  Demodulation         : 0.18
% 4.67/1.93  BG Simplification    : 0.03
% 4.67/1.93  Subsumption          : 0.13
% 4.67/1.93  Abstraction          : 0.04
% 4.67/1.93  MUC search           : 0.00
% 4.67/1.93  Cooper               : 0.00
% 4.67/1.93  Total                : 1.15
% 4.67/1.94  Index Insertion      : 0.00
% 4.67/1.94  Index Deletion       : 0.00
% 4.67/1.94  Index Matching       : 0.00
% 4.67/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
