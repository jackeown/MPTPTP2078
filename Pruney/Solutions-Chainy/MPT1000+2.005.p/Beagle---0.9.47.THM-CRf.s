%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 9.75s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 721 expanded)
%              Number of leaves         :   50 ( 228 expanded)
%              Depth                    :   20
%              Number of atoms          :  221 (1627 expanded)
%              Number of equality atoms :   69 ( 827 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1072,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k8_relset_1(A_182,B_183,C_184,D_185) = k10_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1083,plain,(
    ! [D_185] : k8_relset_1('#skF_5','#skF_6','#skF_7',D_185) = k10_relat_1('#skF_7',D_185) ),
    inference(resolution,[status(thm)],[c_80,c_1072])).

tff(c_76,plain,(
    k8_relset_1('#skF_5','#skF_6','#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1122,plain,(
    k10_relat_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_76])).

tff(c_42,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_304,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_307,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_304])).

tff(c_310,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_307])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_603,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_616,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_603])).

tff(c_1407,plain,(
    ! [B_206,A_207,C_208] :
      ( k1_xboole_0 = B_206
      | k1_relset_1(A_207,B_206,C_208) = A_207
      | ~ v1_funct_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1422,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1407])).

tff(c_1426,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_616,c_1422])).

tff(c_1427,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1426])).

tff(c_411,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_424,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_411])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_470,plain,(
    ! [B_119,A_120] :
      ( k5_relat_1(B_119,k6_relat_1(A_120)) = B_119
      | ~ r1_tarski(k2_relat_1(B_119),A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_962,plain,(
    ! [B_176,A_177] :
      ( k5_relat_1(B_176,k6_relat_1(A_177)) = B_176
      | ~ v5_relat_1(B_176,A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_38,c_470])).

tff(c_52,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_514,plain,(
    ! [A_126,B_127] :
      ( k10_relat_1(A_126,k1_relat_1(B_127)) = k1_relat_1(k5_relat_1(A_126,B_127))
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_532,plain,(
    ! [A_126,A_32] :
      ( k1_relat_1(k5_relat_1(A_126,k6_relat_1(A_32))) = k10_relat_1(A_126,A_32)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_514])).

tff(c_540,plain,(
    ! [A_126,A_32] :
      ( k1_relat_1(k5_relat_1(A_126,k6_relat_1(A_32))) = k10_relat_1(A_126,A_32)
      | ~ v1_relat_1(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_532])).

tff(c_3249,plain,(
    ! [B_317,A_318] :
      ( k10_relat_1(B_317,A_318) = k1_relat_1(B_317)
      | ~ v1_relat_1(B_317)
      | ~ v5_relat_1(B_317,A_318)
      | ~ v1_relat_1(B_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_540])).

tff(c_3273,plain,
    ( k10_relat_1('#skF_7','#skF_6') = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_424,c_3249])).

tff(c_3289,plain,(
    k10_relat_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_1427,c_3273])).

tff(c_3291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1122,c_3289])).

tff(c_3293,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_3292,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_3300,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3293,c_3292])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3295,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_12])).

tff(c_3306,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3295])).

tff(c_3362,plain,(
    ! [A_327,B_328] :
      ( v1_xboole_0(k2_zfmisc_1(A_327,B_328))
      | ~ v1_xboole_0(B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3294,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_14])).

tff(c_3312,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3294])).

tff(c_3371,plain,(
    ! [A_329,B_330] :
      ( k2_zfmisc_1(A_329,B_330) = '#skF_6'
      | ~ v1_xboole_0(B_330) ) ),
    inference(resolution,[status(thm)],[c_3362,c_3312])).

tff(c_3387,plain,(
    ! [A_333] : k2_zfmisc_1(A_333,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3306,c_3371])).

tff(c_3394,plain,(
    v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3387,c_42])).

tff(c_3328,plain,(
    ! [A_321] :
      ( v1_xboole_0(k1_relat_1(A_321))
      | ~ v1_xboole_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3338,plain,(
    ! [A_325] :
      ( k1_relat_1(A_325) = '#skF_6'
      | ~ v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_3328,c_3312])).

tff(c_3346,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3306,c_3338])).

tff(c_3380,plain,(
    ! [A_329] : k2_zfmisc_1(A_329,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3306,c_3371])).

tff(c_3305,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_80])).

tff(c_3386,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3380,c_3305])).

tff(c_30,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3533,plain,(
    ! [A_354,B_355] :
      ( r2_hidden(A_354,B_355)
      | v1_xboole_0(B_355)
      | ~ m1_subset_1(A_354,B_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3541,plain,(
    ! [A_354,A_11] :
      ( r1_tarski(A_354,A_11)
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ m1_subset_1(A_354,k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_3533,c_16])).

tff(c_3550,plain,(
    ! [A_356,A_357] :
      ( r1_tarski(A_356,A_357)
      | ~ m1_subset_1(A_356,k1_zfmisc_1(A_357)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3541])).

tff(c_3554,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3386,c_3550])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3599,plain,(
    ! [C_365,B_366,A_367] :
      ( r2_hidden(C_365,B_366)
      | ~ r2_hidden(C_365,A_367)
      | ~ r1_tarski(A_367,B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3739,plain,(
    ! [A_392,B_393] :
      ( r2_hidden('#skF_1'(A_392),B_393)
      | ~ r1_tarski(A_392,B_393)
      | v1_xboole_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_4,c_3599])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3779,plain,(
    ! [B_396,A_397] :
      ( ~ v1_xboole_0(B_396)
      | ~ r1_tarski(A_397,B_396)
      | v1_xboole_0(A_397) ) ),
    inference(resolution,[status(thm)],[c_3739,c_2])).

tff(c_3785,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3554,c_3779])).

tff(c_3798,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3306,c_3785])).

tff(c_3812,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3798,c_3312])).

tff(c_3612,plain,(
    ! [C_368,B_369,A_370] :
      ( v5_relat_1(C_368,B_369)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_370,B_369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3622,plain,(
    ! [C_371] :
      ( v5_relat_1(C_371,'#skF_6')
      | ~ m1_subset_1(C_371,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3380,c_3612])).

tff(c_3626,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3386,c_3622])).

tff(c_3815,plain,(
    v5_relat_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_3626])).

tff(c_4432,plain,(
    ! [A_459,B_460] :
      ( ~ v1_xboole_0(A_459)
      | v1_xboole_0(k2_relat_1(B_460))
      | ~ v5_relat_1(B_460,A_459)
      | ~ v1_relat_1(B_460) ) ),
    inference(resolution,[status(thm)],[c_38,c_3779])).

tff(c_4434,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3815,c_4432])).

tff(c_4445,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3394,c_3306,c_4434])).

tff(c_3510,plain,(
    ! [A_347,B_348] :
      ( r2_hidden('#skF_2'(A_347,B_348),A_347)
      | r1_tarski(A_347,B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3519,plain,(
    ! [A_347,B_348] :
      ( ~ v1_xboole_0(A_347)
      | r1_tarski(A_347,B_348) ) ),
    inference(resolution,[status(thm)],[c_3510,c_2])).

tff(c_3686,plain,(
    ! [B_384,A_385] :
      ( k5_relat_1(B_384,k6_relat_1(A_385)) = B_384
      | ~ r1_tarski(k2_relat_1(B_384),A_385)
      | ~ v1_relat_1(B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3702,plain,(
    ! [B_384,B_348] :
      ( k5_relat_1(B_384,k6_relat_1(B_348)) = B_384
      | ~ v1_relat_1(B_384)
      | ~ v1_xboole_0(k2_relat_1(B_384)) ) ),
    inference(resolution,[status(thm)],[c_3519,c_3686])).

tff(c_4457,plain,(
    ! [B_348] :
      ( k5_relat_1('#skF_6',k6_relat_1(B_348)) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4445,c_3702])).

tff(c_4554,plain,(
    ! [B_465] : k5_relat_1('#skF_6',k6_relat_1(B_465)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3394,c_4457])).

tff(c_3752,plain,(
    ! [A_394,B_395] :
      ( k10_relat_1(A_394,k1_relat_1(B_395)) = k1_relat_1(k5_relat_1(A_394,B_395))
      | ~ v1_relat_1(B_395)
      | ~ v1_relat_1(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3770,plain,(
    ! [A_394,A_32] :
      ( k1_relat_1(k5_relat_1(A_394,k6_relat_1(A_32))) = k10_relat_1(A_394,A_32)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3752])).

tff(c_3778,plain,(
    ! [A_394,A_32] :
      ( k1_relat_1(k5_relat_1(A_394,k6_relat_1(A_32))) = k10_relat_1(A_394,A_32)
      | ~ v1_relat_1(A_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3770])).

tff(c_4562,plain,(
    ! [B_465] :
      ( k10_relat_1('#skF_6',B_465) = k1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4554,c_3778])).

tff(c_4582,plain,(
    ! [B_465] : k10_relat_1('#skF_6',B_465) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3394,c_3346,c_4562])).

tff(c_3818,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_3386])).

tff(c_4373,plain,(
    ! [A_451,B_452,C_453,D_454] :
      ( k8_relset_1(A_451,B_452,C_453,D_454) = k10_relat_1(C_453,D_454)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14219,plain,(
    ! [A_776,C_777,D_778] :
      ( k8_relset_1(A_776,'#skF_6',C_777,D_778) = k10_relat_1(C_777,D_778)
      | ~ m1_subset_1(C_777,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3380,c_4373])).

tff(c_14221,plain,(
    ! [A_776,D_778] : k8_relset_1(A_776,'#skF_6','#skF_6',D_778) = k10_relat_1('#skF_6',D_778) ),
    inference(resolution,[status(thm)],[c_3818,c_14219])).

tff(c_14223,plain,(
    ! [A_776,D_778] : k8_relset_1(A_776,'#skF_6','#skF_6',D_778) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4582,c_14221])).

tff(c_3347,plain,(
    k8_relset_1('#skF_6','#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3300,c_76])).

tff(c_3819,plain,(
    k8_relset_1('#skF_6','#skF_6','#skF_6','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_3347])).

tff(c_14226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14223,c_3819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.75/3.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.75/3.32  
% 9.75/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.75/3.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 9.75/3.32  
% 9.75/3.32  %Foreground sorts:
% 9.75/3.32  
% 9.75/3.32  
% 9.75/3.32  %Background operators:
% 9.75/3.32  
% 9.75/3.32  
% 9.75/3.32  %Foreground operators:
% 9.75/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.75/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.75/3.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 9.75/3.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.75/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.75/3.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.75/3.32  tff('#skF_7', type, '#skF_7': $i).
% 9.75/3.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.75/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.75/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.75/3.32  tff('#skF_5', type, '#skF_5': $i).
% 9.75/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.75/3.32  tff('#skF_6', type, '#skF_6': $i).
% 9.75/3.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.75/3.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.75/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.75/3.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.75/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.75/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.75/3.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.75/3.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.75/3.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.75/3.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.75/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.75/3.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.75/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.75/3.32  
% 10.03/3.34  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 10.03/3.34  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 10.03/3.34  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.03/3.34  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.03/3.34  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.03/3.34  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.03/3.34  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.03/3.34  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.03/3.34  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 10.03/3.34  tff(f_103, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.03/3.34  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.03/3.34  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 10.03/3.34  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.03/3.34  tff(f_54, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 10.03/3.34  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.03/3.34  tff(f_80, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 10.03/3.34  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.03/3.34  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.03/3.34  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.03/3.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.03/3.34  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.03/3.34  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.03/3.34  tff(c_1072, plain, (![A_182, B_183, C_184, D_185]: (k8_relset_1(A_182, B_183, C_184, D_185)=k10_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.03/3.34  tff(c_1083, plain, (![D_185]: (k8_relset_1('#skF_5', '#skF_6', '#skF_7', D_185)=k10_relat_1('#skF_7', D_185))), inference(resolution, [status(thm)], [c_80, c_1072])).
% 10.03/3.34  tff(c_76, plain, (k8_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.03/3.34  tff(c_1122, plain, (k10_relat_1('#skF_7', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_76])).
% 10.03/3.34  tff(c_42, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.03/3.34  tff(c_304, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.03/3.34  tff(c_307, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_304])).
% 10.03/3.34  tff(c_310, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_307])).
% 10.03/3.34  tff(c_78, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.03/3.34  tff(c_104, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_78])).
% 10.03/3.34  tff(c_82, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.03/3.34  tff(c_603, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.03/3.34  tff(c_616, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_603])).
% 10.03/3.34  tff(c_1407, plain, (![B_206, A_207, C_208]: (k1_xboole_0=B_206 | k1_relset_1(A_207, B_206, C_208)=A_207 | ~v1_funct_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.03/3.34  tff(c_1422, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_1407])).
% 10.03/3.34  tff(c_1426, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_616, c_1422])).
% 10.03/3.34  tff(c_1427, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_104, c_1426])).
% 10.03/3.34  tff(c_411, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.03/3.34  tff(c_424, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_411])).
% 10.03/3.34  tff(c_38, plain, (![B_25, A_24]: (r1_tarski(k2_relat_1(B_25), A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.03/3.34  tff(c_470, plain, (![B_119, A_120]: (k5_relat_1(B_119, k6_relat_1(A_120))=B_119 | ~r1_tarski(k2_relat_1(B_119), A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.03/3.34  tff(c_962, plain, (![B_176, A_177]: (k5_relat_1(B_176, k6_relat_1(A_177))=B_176 | ~v5_relat_1(B_176, A_177) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_38, c_470])).
% 10.03/3.34  tff(c_52, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.03/3.34  tff(c_46, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.03/3.34  tff(c_514, plain, (![A_126, B_127]: (k10_relat_1(A_126, k1_relat_1(B_127))=k1_relat_1(k5_relat_1(A_126, B_127)) | ~v1_relat_1(B_127) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.03/3.34  tff(c_532, plain, (![A_126, A_32]: (k1_relat_1(k5_relat_1(A_126, k6_relat_1(A_32)))=k10_relat_1(A_126, A_32) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_46, c_514])).
% 10.03/3.34  tff(c_540, plain, (![A_126, A_32]: (k1_relat_1(k5_relat_1(A_126, k6_relat_1(A_32)))=k10_relat_1(A_126, A_32) | ~v1_relat_1(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_532])).
% 10.03/3.34  tff(c_3249, plain, (![B_317, A_318]: (k10_relat_1(B_317, A_318)=k1_relat_1(B_317) | ~v1_relat_1(B_317) | ~v5_relat_1(B_317, A_318) | ~v1_relat_1(B_317))), inference(superposition, [status(thm), theory('equality')], [c_962, c_540])).
% 10.03/3.34  tff(c_3273, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_424, c_3249])).
% 10.03/3.34  tff(c_3289, plain, (k10_relat_1('#skF_7', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_1427, c_3273])).
% 10.03/3.34  tff(c_3291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1122, c_3289])).
% 10.03/3.34  tff(c_3293, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_78])).
% 10.03/3.34  tff(c_3292, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_78])).
% 10.03/3.34  tff(c_3300, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3293, c_3292])).
% 10.03/3.34  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.03/3.34  tff(c_3295, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_12])).
% 10.03/3.34  tff(c_3306, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3295])).
% 10.03/3.34  tff(c_3362, plain, (![A_327, B_328]: (v1_xboole_0(k2_zfmisc_1(A_327, B_328)) | ~v1_xboole_0(B_328))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.03/3.34  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.03/3.34  tff(c_3294, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_14])).
% 10.03/3.34  tff(c_3312, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3294])).
% 10.03/3.34  tff(c_3371, plain, (![A_329, B_330]: (k2_zfmisc_1(A_329, B_330)='#skF_6' | ~v1_xboole_0(B_330))), inference(resolution, [status(thm)], [c_3362, c_3312])).
% 10.03/3.34  tff(c_3387, plain, (![A_333]: (k2_zfmisc_1(A_333, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_3306, c_3371])).
% 10.03/3.34  tff(c_3394, plain, (v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3387, c_42])).
% 10.03/3.34  tff(c_3328, plain, (![A_321]: (v1_xboole_0(k1_relat_1(A_321)) | ~v1_xboole_0(A_321))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.03/3.34  tff(c_3338, plain, (![A_325]: (k1_relat_1(A_325)='#skF_6' | ~v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_3328, c_3312])).
% 10.03/3.34  tff(c_3346, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3306, c_3338])).
% 10.03/3.34  tff(c_3380, plain, (![A_329]: (k2_zfmisc_1(A_329, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_3306, c_3371])).
% 10.03/3.34  tff(c_3305, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_80])).
% 10.03/3.34  tff(c_3386, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3380, c_3305])).
% 10.03/3.34  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.03/3.34  tff(c_3533, plain, (![A_354, B_355]: (r2_hidden(A_354, B_355) | v1_xboole_0(B_355) | ~m1_subset_1(A_354, B_355))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.03/3.34  tff(c_16, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.34  tff(c_3541, plain, (![A_354, A_11]: (r1_tarski(A_354, A_11) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~m1_subset_1(A_354, k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_3533, c_16])).
% 10.03/3.34  tff(c_3550, plain, (![A_356, A_357]: (r1_tarski(A_356, A_357) | ~m1_subset_1(A_356, k1_zfmisc_1(A_357)))), inference(negUnitSimplification, [status(thm)], [c_30, c_3541])).
% 10.03/3.34  tff(c_3554, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3386, c_3550])).
% 10.03/3.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.03/3.34  tff(c_3599, plain, (![C_365, B_366, A_367]: (r2_hidden(C_365, B_366) | ~r2_hidden(C_365, A_367) | ~r1_tarski(A_367, B_366))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.03/3.34  tff(c_3739, plain, (![A_392, B_393]: (r2_hidden('#skF_1'(A_392), B_393) | ~r1_tarski(A_392, B_393) | v1_xboole_0(A_392))), inference(resolution, [status(thm)], [c_4, c_3599])).
% 10.03/3.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.03/3.34  tff(c_3779, plain, (![B_396, A_397]: (~v1_xboole_0(B_396) | ~r1_tarski(A_397, B_396) | v1_xboole_0(A_397))), inference(resolution, [status(thm)], [c_3739, c_2])).
% 10.03/3.34  tff(c_3785, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_3554, c_3779])).
% 10.03/3.34  tff(c_3798, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3306, c_3785])).
% 10.03/3.34  tff(c_3812, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3798, c_3312])).
% 10.03/3.34  tff(c_3612, plain, (![C_368, B_369, A_370]: (v5_relat_1(C_368, B_369) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_370, B_369))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.03/3.34  tff(c_3622, plain, (![C_371]: (v5_relat_1(C_371, '#skF_6') | ~m1_subset_1(C_371, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3380, c_3612])).
% 10.03/3.34  tff(c_3626, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3386, c_3622])).
% 10.03/3.34  tff(c_3815, plain, (v5_relat_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3812, c_3626])).
% 10.03/3.34  tff(c_4432, plain, (![A_459, B_460]: (~v1_xboole_0(A_459) | v1_xboole_0(k2_relat_1(B_460)) | ~v5_relat_1(B_460, A_459) | ~v1_relat_1(B_460))), inference(resolution, [status(thm)], [c_38, c_3779])).
% 10.03/3.34  tff(c_4434, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3815, c_4432])).
% 10.03/3.34  tff(c_4445, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3394, c_3306, c_4434])).
% 10.03/3.34  tff(c_3510, plain, (![A_347, B_348]: (r2_hidden('#skF_2'(A_347, B_348), A_347) | r1_tarski(A_347, B_348))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.03/3.34  tff(c_3519, plain, (![A_347, B_348]: (~v1_xboole_0(A_347) | r1_tarski(A_347, B_348))), inference(resolution, [status(thm)], [c_3510, c_2])).
% 10.03/3.34  tff(c_3686, plain, (![B_384, A_385]: (k5_relat_1(B_384, k6_relat_1(A_385))=B_384 | ~r1_tarski(k2_relat_1(B_384), A_385) | ~v1_relat_1(B_384))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.03/3.34  tff(c_3702, plain, (![B_384, B_348]: (k5_relat_1(B_384, k6_relat_1(B_348))=B_384 | ~v1_relat_1(B_384) | ~v1_xboole_0(k2_relat_1(B_384)))), inference(resolution, [status(thm)], [c_3519, c_3686])).
% 10.03/3.34  tff(c_4457, plain, (![B_348]: (k5_relat_1('#skF_6', k6_relat_1(B_348))='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4445, c_3702])).
% 10.03/3.34  tff(c_4554, plain, (![B_465]: (k5_relat_1('#skF_6', k6_relat_1(B_465))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3394, c_4457])).
% 10.03/3.34  tff(c_3752, plain, (![A_394, B_395]: (k10_relat_1(A_394, k1_relat_1(B_395))=k1_relat_1(k5_relat_1(A_394, B_395)) | ~v1_relat_1(B_395) | ~v1_relat_1(A_394))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.03/3.34  tff(c_3770, plain, (![A_394, A_32]: (k1_relat_1(k5_relat_1(A_394, k6_relat_1(A_32)))=k10_relat_1(A_394, A_32) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(A_394))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3752])).
% 10.03/3.34  tff(c_3778, plain, (![A_394, A_32]: (k1_relat_1(k5_relat_1(A_394, k6_relat_1(A_32)))=k10_relat_1(A_394, A_32) | ~v1_relat_1(A_394))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3770])).
% 10.03/3.34  tff(c_4562, plain, (![B_465]: (k10_relat_1('#skF_6', B_465)=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4554, c_3778])).
% 10.03/3.34  tff(c_4582, plain, (![B_465]: (k10_relat_1('#skF_6', B_465)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3394, c_3346, c_4562])).
% 10.03/3.34  tff(c_3818, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3812, c_3386])).
% 10.03/3.34  tff(c_4373, plain, (![A_451, B_452, C_453, D_454]: (k8_relset_1(A_451, B_452, C_453, D_454)=k10_relat_1(C_453, D_454) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.03/3.34  tff(c_14219, plain, (![A_776, C_777, D_778]: (k8_relset_1(A_776, '#skF_6', C_777, D_778)=k10_relat_1(C_777, D_778) | ~m1_subset_1(C_777, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3380, c_4373])).
% 10.03/3.34  tff(c_14221, plain, (![A_776, D_778]: (k8_relset_1(A_776, '#skF_6', '#skF_6', D_778)=k10_relat_1('#skF_6', D_778))), inference(resolution, [status(thm)], [c_3818, c_14219])).
% 10.03/3.34  tff(c_14223, plain, (![A_776, D_778]: (k8_relset_1(A_776, '#skF_6', '#skF_6', D_778)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4582, c_14221])).
% 10.03/3.34  tff(c_3347, plain, (k8_relset_1('#skF_6', '#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3300, c_76])).
% 10.03/3.34  tff(c_3819, plain, (k8_relset_1('#skF_6', '#skF_6', '#skF_6', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3812, c_3347])).
% 10.03/3.34  tff(c_14226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14223, c_3819])).
% 10.03/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.03/3.34  
% 10.03/3.34  Inference rules
% 10.03/3.34  ----------------------
% 10.03/3.34  #Ref     : 0
% 10.03/3.34  #Sup     : 3180
% 10.03/3.34  #Fact    : 0
% 10.03/3.34  #Define  : 0
% 10.03/3.34  #Split   : 19
% 10.03/3.34  #Chain   : 0
% 10.03/3.34  #Close   : 0
% 10.03/3.34  
% 10.03/3.34  Ordering : KBO
% 10.03/3.34  
% 10.03/3.34  Simplification rules
% 10.03/3.34  ----------------------
% 10.03/3.34  #Subsume      : 984
% 10.03/3.34  #Demod        : 2107
% 10.03/3.34  #Tautology    : 1178
% 10.03/3.34  #SimpNegUnit  : 338
% 10.03/3.34  #BackRed      : 98
% 10.03/3.34  
% 10.03/3.34  #Partial instantiations: 0
% 10.03/3.34  #Strategies tried      : 1
% 10.03/3.34  
% 10.03/3.34  Timing (in seconds)
% 10.03/3.34  ----------------------
% 10.03/3.35  Preprocessing        : 0.39
% 10.03/3.35  Parsing              : 0.19
% 10.03/3.35  CNF conversion       : 0.03
% 10.03/3.35  Main loop            : 2.15
% 10.03/3.35  Inferencing          : 0.65
% 10.03/3.35  Reduction            : 0.68
% 10.03/3.35  Demodulation         : 0.46
% 10.03/3.35  BG Simplification    : 0.07
% 10.03/3.35  Subsumption          : 0.59
% 10.03/3.35  Abstraction          : 0.08
% 10.03/3.35  MUC search           : 0.00
% 10.03/3.35  Cooper               : 0.00
% 10.03/3.35  Total                : 2.59
% 10.03/3.35  Index Insertion      : 0.00
% 10.03/3.35  Index Deletion       : 0.00
% 10.03/3.35  Index Matching       : 0.00
% 10.03/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
