%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 337 expanded)
%              Number of leaves         :   34 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 (1020 expanded)
%              Number of equality atoms :   35 ( 144 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_960,plain,(
    ! [A_165,B_166,C_167] :
      ( k2_relset_1(A_165,B_166,C_167) = k2_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_975,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_960])).

tff(c_1305,plain,(
    ! [D_202,C_203,A_204,B_205] :
      ( r2_hidden(k1_funct_1(D_202,C_203),k2_relset_1(A_204,B_205,D_202))
      | k1_xboole_0 = B_205
      | ~ r2_hidden(C_203,A_204)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_2(D_202,A_204,B_205)
      | ~ v1_funct_1(D_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1322,plain,(
    ! [C_203] :
      ( r2_hidden(k1_funct_1('#skF_6',C_203),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_203,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_1305])).

tff(c_1332,plain,(
    ! [C_203] :
      ( r2_hidden(k1_funct_1('#skF_6',C_203),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_203,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1322])).

tff(c_3529,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1332])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_xboole_0(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_234,plain,(
    ! [C_85,A_10] :
      ( v1_xboole_0(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_224])).

tff(c_240,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_248,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_18])).

tff(c_302,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_317,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_302])).

tff(c_375,plain,(
    ! [D_112,C_113,A_114,B_115] :
      ( r2_hidden(k1_funct_1(D_112,C_113),k2_relset_1(A_114,B_115,D_112))
      | k1_xboole_0 = B_115
      | ~ r2_hidden(C_113,A_114)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2(D_112,A_114,B_115)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_383,plain,(
    ! [C_113] :
      ( r2_hidden(k1_funct_1('#skF_6',C_113),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_113,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_375])).

tff(c_387,plain,(
    ! [C_113] :
      ( r2_hidden(k1_funct_1('#skF_6',C_113),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_113,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_383])).

tff(c_408,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_411,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_408,c_14])).

tff(c_421,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_38])).

tff(c_16,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_412,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_4',B_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_408,c_16])).

tff(c_315,plain,(
    ! [B_11,C_101] :
      ( k2_relset_1(k1_xboole_0,B_11,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_302])).

tff(c_716,plain,(
    ! [B_147,C_148] :
      ( k2_relset_1('#skF_4',B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_408,c_315])).

tff(c_768,plain,(
    ! [B_149] : k2_relset_1('#skF_4',B_149,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_421,c_716])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k2_relset_1(A_22,B_23,C_24),k1_zfmisc_1(B_23))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_776,plain,(
    ! [B_149] :
      ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(B_149))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_149))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_28])).

tff(c_789,plain,(
    ! [B_150] : m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(B_150)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_412,c_776])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_822,plain,(
    ! [B_151] : r1_tarski(k2_relat_1('#skF_6'),B_151) ),
    inference(resolution,[status(thm)],[c_789,c_20])).

tff(c_73,plain,(
    ! [A_53] :
      ( v1_xboole_0(A_53)
      | r2_hidden('#skF_1'(A_53),A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_53] :
      ( ~ r1_tarski(A_53,'#skF_1'(A_53))
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_73,c_24])).

tff(c_249,plain,(
    ! [A_53] : ~ r1_tarski(A_53,'#skF_1'(A_53)) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_80])).

tff(c_856,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_822,c_249])).

tff(c_857,plain,(
    ! [C_113] :
      ( r2_hidden(k1_funct_1('#skF_6',C_113),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_113,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k3_funct_2(A_28,B_29,C_30,D_31) = k1_funct_1(C_30,D_31)
      | ~ m1_subset_1(D_31,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_869,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k3_funct_2(A_154,B_155,C_156,D_157) = k1_funct_1(C_156,D_157)
      | ~ m1_subset_1(D_157,A_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_2(C_156,A_154,B_155)
      | ~ v1_funct_1(C_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_32])).

tff(c_901,plain,(
    ! [B_162,C_163] :
      ( k3_funct_2('#skF_3',B_162,C_163,'#skF_5') = k1_funct_1(C_163,'#skF_5')
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_162)))
      | ~ v1_funct_2(C_163,'#skF_3',B_162)
      | ~ v1_funct_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_44,c_869])).

tff(c_912,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_901])).

tff(c_921,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5') = k1_funct_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_912])).

tff(c_36,plain,(
    ~ r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5'),k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_319,plain,(
    ~ r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_36])).

tff(c_939,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_319])).

tff(c_950,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_857,c_939])).

tff(c_954,plain,(
    ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_248,c_950])).

tff(c_958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_954])).

tff(c_976,plain,(
    ! [C_168] :
      ( v1_xboole_0(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_982,plain,(
    ! [A_169] :
      ( v1_xboole_0(A_169)
      | ~ r1_tarski(A_169,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_976])).

tff(c_991,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_141,c_982])).

tff(c_3577,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3529,c_991])).

tff(c_3585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3577])).

tff(c_3588,plain,(
    ! [C_305] :
      ( r2_hidden(k1_funct_1('#skF_6',C_305),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_305,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_1117,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k3_funct_2(A_188,B_189,C_190,D_191) = k1_funct_1(C_190,D_191)
      | ~ m1_subset_1(D_191,A_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_190,A_188,B_189)
      | ~ v1_funct_1(C_190)
      | v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1127,plain,(
    ! [B_189,C_190] :
      ( k3_funct_2('#skF_3',B_189,C_190,'#skF_5') = k1_funct_1(C_190,'#skF_5')
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_189)))
      | ~ v1_funct_2(C_190,'#skF_3',B_189)
      | ~ v1_funct_1(C_190)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_1117])).

tff(c_1165,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_3',B_195,C_196,'#skF_5') = k1_funct_1(C_196,'#skF_5')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_195)))
      | ~ v1_funct_2(C_196,'#skF_3',B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1127])).

tff(c_1176,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1165])).

tff(c_1185,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5') = k1_funct_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1176])).

tff(c_993,plain,(
    ~ r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_36])).

tff(c_1187,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_993])).

tff(c_3603,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_3588,c_1187])).

tff(c_3615,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_3603])).

tff(c_3618,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3615])).

tff(c_3620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.84  
% 4.79/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.84  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.79/1.84  
% 4.79/1.84  %Foreground sorts:
% 4.79/1.84  
% 4.79/1.84  
% 4.79/1.84  %Background operators:
% 4.79/1.84  
% 4.79/1.84  
% 4.79/1.84  %Foreground operators:
% 4.79/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.79/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.79/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.79/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.79/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.79/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.79/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.79/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.79/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.79/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.79/1.84  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.79/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.84  
% 4.79/1.86  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 4.79/1.86  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.79/1.86  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.79/1.86  tff(f_99, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 4.79/1.86  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.79/1.86  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.79/1.86  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.79/1.86  tff(f_66, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.79/1.86  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.79/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.79/1.86  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.79/1.86  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.79/1.86  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_18, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.79/1.86  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_960, plain, (![A_165, B_166, C_167]: (k2_relset_1(A_165, B_166, C_167)=k2_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.86  tff(c_975, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_960])).
% 4.79/1.86  tff(c_1305, plain, (![D_202, C_203, A_204, B_205]: (r2_hidden(k1_funct_1(D_202, C_203), k2_relset_1(A_204, B_205, D_202)) | k1_xboole_0=B_205 | ~r2_hidden(C_203, A_204) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_2(D_202, A_204, B_205) | ~v1_funct_1(D_202))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.79/1.86  tff(c_1322, plain, (![C_203]: (r2_hidden(k1_funct_1('#skF_6', C_203), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_203, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_975, c_1305])).
% 4.79/1.86  tff(c_1332, plain, (![C_203]: (r2_hidden(k1_funct_1('#skF_6', C_203), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_203, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1322])).
% 4.79/1.86  tff(c_3529, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1332])).
% 4.79/1.86  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.79/1.86  tff(c_132, plain, (![A_67, B_68]: (~r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.79/1.86  tff(c_141, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_132])).
% 4.79/1.86  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.79/1.86  tff(c_14, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.79/1.86  tff(c_224, plain, (![C_85, A_86, B_87]: (v1_xboole_0(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.79/1.86  tff(c_234, plain, (![C_85, A_10]: (v1_xboole_0(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_224])).
% 4.79/1.86  tff(c_240, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitLeft, [status(thm)], [c_234])).
% 4.79/1.86  tff(c_248, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | ~m1_subset_1(A_12, B_13))), inference(negUnitSimplification, [status(thm)], [c_240, c_18])).
% 4.79/1.86  tff(c_302, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.86  tff(c_317, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_302])).
% 4.79/1.86  tff(c_375, plain, (![D_112, C_113, A_114, B_115]: (r2_hidden(k1_funct_1(D_112, C_113), k2_relset_1(A_114, B_115, D_112)) | k1_xboole_0=B_115 | ~r2_hidden(C_113, A_114) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2(D_112, A_114, B_115) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.79/1.86  tff(c_383, plain, (![C_113]: (r2_hidden(k1_funct_1('#skF_6', C_113), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_113, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_375])).
% 4.79/1.86  tff(c_387, plain, (![C_113]: (r2_hidden(k1_funct_1('#skF_6', C_113), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_113, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_383])).
% 4.79/1.86  tff(c_408, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_387])).
% 4.79/1.86  tff(c_411, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_408, c_14])).
% 4.79/1.86  tff(c_421, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_38])).
% 4.79/1.86  tff(c_16, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.79/1.86  tff(c_412, plain, (![B_11]: (k2_zfmisc_1('#skF_4', B_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_408, c_16])).
% 4.79/1.86  tff(c_315, plain, (![B_11, C_101]: (k2_relset_1(k1_xboole_0, B_11, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_302])).
% 4.79/1.86  tff(c_716, plain, (![B_147, C_148]: (k2_relset_1('#skF_4', B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_408, c_315])).
% 4.79/1.86  tff(c_768, plain, (![B_149]: (k2_relset_1('#skF_4', B_149, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_421, c_716])).
% 4.79/1.86  tff(c_28, plain, (![A_22, B_23, C_24]: (m1_subset_1(k2_relset_1(A_22, B_23, C_24), k1_zfmisc_1(B_23)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.86  tff(c_776, plain, (![B_149]: (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(B_149)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_149))))), inference(superposition, [status(thm), theory('equality')], [c_768, c_28])).
% 4.79/1.86  tff(c_789, plain, (![B_150]: (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(B_150)))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_412, c_776])).
% 4.79/1.86  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.79/1.86  tff(c_822, plain, (![B_151]: (r1_tarski(k2_relat_1('#skF_6'), B_151))), inference(resolution, [status(thm)], [c_789, c_20])).
% 4.79/1.86  tff(c_73, plain, (![A_53]: (v1_xboole_0(A_53) | r2_hidden('#skF_1'(A_53), A_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.79/1.86  tff(c_24, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.79/1.86  tff(c_80, plain, (![A_53]: (~r1_tarski(A_53, '#skF_1'(A_53)) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_73, c_24])).
% 4.79/1.86  tff(c_249, plain, (![A_53]: (~r1_tarski(A_53, '#skF_1'(A_53)))), inference(negUnitSimplification, [status(thm)], [c_240, c_80])).
% 4.79/1.86  tff(c_856, plain, $false, inference(resolution, [status(thm)], [c_822, c_249])).
% 4.79/1.86  tff(c_857, plain, (![C_113]: (r2_hidden(k1_funct_1('#skF_6', C_113), k2_relat_1('#skF_6')) | ~r2_hidden(C_113, '#skF_3'))), inference(splitRight, [status(thm)], [c_387])).
% 4.79/1.86  tff(c_32, plain, (![A_28, B_29, C_30, D_31]: (k3_funct_2(A_28, B_29, C_30, D_31)=k1_funct_1(C_30, D_31) | ~m1_subset_1(D_31, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.79/1.86  tff(c_869, plain, (![A_154, B_155, C_156, D_157]: (k3_funct_2(A_154, B_155, C_156, D_157)=k1_funct_1(C_156, D_157) | ~m1_subset_1(D_157, A_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_2(C_156, A_154, B_155) | ~v1_funct_1(C_156))), inference(negUnitSimplification, [status(thm)], [c_240, c_32])).
% 4.79/1.86  tff(c_901, plain, (![B_162, C_163]: (k3_funct_2('#skF_3', B_162, C_163, '#skF_5')=k1_funct_1(C_163, '#skF_5') | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_162))) | ~v1_funct_2(C_163, '#skF_3', B_162) | ~v1_funct_1(C_163))), inference(resolution, [status(thm)], [c_44, c_869])).
% 4.79/1.86  tff(c_912, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_901])).
% 4.79/1.86  tff(c_921, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5')=k1_funct_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_912])).
% 4.79/1.86  tff(c_36, plain, (~r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5'), k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.86  tff(c_319, plain, (~r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_36])).
% 4.79/1.86  tff(c_939, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_921, c_319])).
% 4.79/1.86  tff(c_950, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_857, c_939])).
% 4.79/1.86  tff(c_954, plain, (~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_248, c_950])).
% 4.79/1.86  tff(c_958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_954])).
% 4.79/1.86  tff(c_976, plain, (![C_168]: (v1_xboole_0(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_234])).
% 4.79/1.86  tff(c_982, plain, (![A_169]: (v1_xboole_0(A_169) | ~r1_tarski(A_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_976])).
% 4.79/1.86  tff(c_991, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_141, c_982])).
% 4.79/1.86  tff(c_3577, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3529, c_991])).
% 4.79/1.86  tff(c_3585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_3577])).
% 4.79/1.86  tff(c_3588, plain, (![C_305]: (r2_hidden(k1_funct_1('#skF_6', C_305), k2_relat_1('#skF_6')) | ~r2_hidden(C_305, '#skF_3'))), inference(splitRight, [status(thm)], [c_1332])).
% 4.79/1.86  tff(c_1117, plain, (![A_188, B_189, C_190, D_191]: (k3_funct_2(A_188, B_189, C_190, D_191)=k1_funct_1(C_190, D_191) | ~m1_subset_1(D_191, A_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2(C_190, A_188, B_189) | ~v1_funct_1(C_190) | v1_xboole_0(A_188))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.79/1.86  tff(c_1127, plain, (![B_189, C_190]: (k3_funct_2('#skF_3', B_189, C_190, '#skF_5')=k1_funct_1(C_190, '#skF_5') | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_189))) | ~v1_funct_2(C_190, '#skF_3', B_189) | ~v1_funct_1(C_190) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1117])).
% 4.79/1.86  tff(c_1165, plain, (![B_195, C_196]: (k3_funct_2('#skF_3', B_195, C_196, '#skF_5')=k1_funct_1(C_196, '#skF_5') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_195))) | ~v1_funct_2(C_196, '#skF_3', B_195) | ~v1_funct_1(C_196))), inference(negUnitSimplification, [status(thm)], [c_48, c_1127])).
% 4.79/1.86  tff(c_1176, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1165])).
% 4.79/1.86  tff(c_1185, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5')=k1_funct_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1176])).
% 4.79/1.86  tff(c_993, plain, (~r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_975, c_36])).
% 4.79/1.86  tff(c_1187, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_993])).
% 4.79/1.86  tff(c_3603, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_3588, c_1187])).
% 4.79/1.86  tff(c_3615, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_3603])).
% 4.79/1.86  tff(c_3618, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3615])).
% 4.79/1.86  tff(c_3620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3618])).
% 4.79/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.86  
% 4.79/1.86  Inference rules
% 4.79/1.86  ----------------------
% 4.79/1.86  #Ref     : 0
% 4.79/1.86  #Sup     : 748
% 4.79/1.86  #Fact    : 0
% 4.79/1.86  #Define  : 0
% 4.79/1.86  #Split   : 18
% 4.79/1.86  #Chain   : 0
% 4.79/1.86  #Close   : 0
% 4.79/1.86  
% 4.79/1.86  Ordering : KBO
% 4.79/1.86  
% 4.79/1.86  Simplification rules
% 4.79/1.86  ----------------------
% 4.79/1.86  #Subsume      : 86
% 4.79/1.86  #Demod        : 504
% 4.79/1.86  #Tautology    : 306
% 4.79/1.86  #SimpNegUnit  : 19
% 4.79/1.86  #BackRed      : 79
% 4.79/1.86  
% 4.79/1.86  #Partial instantiations: 0
% 4.79/1.86  #Strategies tried      : 1
% 4.79/1.86  
% 4.79/1.86  Timing (in seconds)
% 4.79/1.86  ----------------------
% 4.79/1.86  Preprocessing        : 0.32
% 4.79/1.86  Parsing              : 0.17
% 4.79/1.86  CNF conversion       : 0.02
% 4.79/1.86  Main loop            : 0.77
% 4.79/1.86  Inferencing          : 0.27
% 4.79/1.86  Reduction            : 0.25
% 4.79/1.86  Demodulation         : 0.18
% 4.79/1.86  BG Simplification    : 0.03
% 4.79/1.86  Subsumption          : 0.15
% 4.79/1.86  Abstraction          : 0.04
% 4.79/1.86  MUC search           : 0.00
% 4.79/1.86  Cooper               : 0.00
% 4.79/1.86  Total                : 1.13
% 4.79/1.86  Index Insertion      : 0.00
% 4.79/1.86  Index Deletion       : 0.00
% 4.79/1.86  Index Matching       : 0.00
% 4.79/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
