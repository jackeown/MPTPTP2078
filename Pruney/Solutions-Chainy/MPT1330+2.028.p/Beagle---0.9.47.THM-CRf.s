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
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 612 expanded)
%              Number of leaves         :   36 ( 233 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 (1477 expanded)
%              Number of equality atoms :   79 ( 735 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_8,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_102,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_48,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_101,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_124,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_101,c_42])).

tff(c_135,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_135])).

tff(c_188,plain,(
    ! [A_63,B_64,C_65] :
      ( k8_relset_1(A_63,B_64,C_65,B_64) = k1_relset_1(A_63,B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_190,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_188])).

tff(c_196,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_190])).

tff(c_38,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_130,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_101,c_38])).

tff(c_197,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_130])).

tff(c_40,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_93,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_103,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_44])).

tff(c_123,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103])).

tff(c_169,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k7_relset_1(A_52,B_53,C_54,D_55) = k9_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_176,plain,(
    ! [D_55] : k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_55) = k9_relat_1('#skF_3',D_55) ),
    inference(resolution,[status(thm)],[c_124,c_169])).

tff(c_152,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_152])).

tff(c_202,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_relset_1(A_66,B_67,C_68,A_66) = k2_relset_1(A_66,B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_204,plain,(
    k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_1')) = k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_202])).

tff(c_210,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_162,c_204])).

tff(c_216,plain,(
    ! [B_71,A_72,C_73] :
      ( k8_relset_1(B_71,A_72,C_73,k7_relset_1(B_71,A_72,C_73,B_71)) = k1_relset_1(B_71,A_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_218,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_1'))) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_216])).

tff(c_224,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_176,c_145,c_218])).

tff(c_248,plain,(
    ! [B_89,A_90,C_91] :
      ( k1_xboole_0 = B_89
      | k8_relset_1(A_90,B_89,C_91,k7_relset_1(A_90,B_89,C_91,A_90)) = A_90
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_250,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_248])).

tff(c_257,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_123,c_224,c_210,c_176,c_250])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_93,c_257])).

tff(c_261,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_270,plain,(
    ! [A_92] :
      ( u1_struct_0(A_92) = k2_struct_0(A_92)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_273,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_270])).

tff(c_278,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273])).

tff(c_302,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_278,c_42])).

tff(c_304,plain,(
    ! [A_95,B_96] :
      ( k9_relat_1(k6_relat_1(A_95),B_96) = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_302,c_304])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_307])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_322,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_12])).

tff(c_311,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_302])).

tff(c_362,plain,(
    ! [A_100] : k2_zfmisc_1(A_100,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_4])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,(
    ! [A_112,C_113] :
      ( k1_relset_1(A_112,'#skF_3',C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_18])).

tff(c_423,plain,(
    ! [A_112] : k1_relset_1(A_112,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_421])).

tff(c_425,plain,(
    ! [A_112] : k1_relset_1(A_112,'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_423])).

tff(c_320,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_4])).

tff(c_490,plain,(
    ! [A_127,B_128,C_129] :
      ( k8_relset_1(A_127,B_128,C_129,B_128) = k1_relset_1(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_527,plain,(
    ! [A_140,C_141] :
      ( k8_relset_1(A_140,'#skF_3',C_141,'#skF_3') = k1_relset_1(A_140,'#skF_3',C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_490])).

tff(c_529,plain,(
    ! [A_140] : k8_relset_1(A_140,'#skF_3','#skF_3','#skF_3') = k1_relset_1(A_140,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_527])).

tff(c_531,plain,(
    ! [A_140] : k8_relset_1(A_140,'#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_529])).

tff(c_260,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_276,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_270])).

tff(c_280,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_276])).

tff(c_303,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_278,c_261,c_260,c_38])).

tff(c_310,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_309,c_309,c_303])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.83  
% 3.51/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.84  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.51/1.84  
% 3.51/1.84  %Foreground sorts:
% 3.51/1.84  
% 3.51/1.84  
% 3.51/1.84  %Background operators:
% 3.51/1.84  
% 3.51/1.84  
% 3.51/1.84  %Foreground operators:
% 3.51/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.51/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.51/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.51/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.51/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.84  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.51/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.51/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.51/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.84  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.51/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.84  
% 3.51/1.86  tff(f_33, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.51/1.86  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.51/1.86  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.51/1.86  tff(f_100, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 3.51/1.86  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.51/1.86  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.51/1.86  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.51/1.86  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.51/1.86  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.51/1.86  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.51/1.86  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 3.51/1.86  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.51/1.86  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.51/1.86  tff(c_8, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.51/1.86  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.51/1.86  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.86  tff(c_50, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.86  tff(c_94, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.51/1.86  tff(c_102, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_94])).
% 3.51/1.86  tff(c_48, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.86  tff(c_101, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_94])).
% 3.51/1.86  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.86  tff(c_124, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_101, c_42])).
% 3.51/1.87  tff(c_135, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.87  tff(c_145, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_135])).
% 3.51/1.87  tff(c_188, plain, (![A_63, B_64, C_65]: (k8_relset_1(A_63, B_64, C_65, B_64)=k1_relset_1(A_63, B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.51/1.87  tff(c_190, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_188])).
% 3.51/1.87  tff(c_196, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_190])).
% 3.51/1.87  tff(c_38, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.87  tff(c_130, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_101, c_38])).
% 3.51/1.87  tff(c_197, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_130])).
% 3.51/1.87  tff(c_40, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.87  tff(c_93, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.51/1.87  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.87  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.87  tff(c_103, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_44])).
% 3.51/1.87  tff(c_123, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103])).
% 3.51/1.87  tff(c_169, plain, (![A_52, B_53, C_54, D_55]: (k7_relset_1(A_52, B_53, C_54, D_55)=k9_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.51/1.87  tff(c_176, plain, (![D_55]: (k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_55)=k9_relat_1('#skF_3', D_55))), inference(resolution, [status(thm)], [c_124, c_169])).
% 3.51/1.87  tff(c_152, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.51/1.87  tff(c_162, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_152])).
% 3.51/1.87  tff(c_202, plain, (![A_66, B_67, C_68]: (k7_relset_1(A_66, B_67, C_68, A_66)=k2_relset_1(A_66, B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.51/1.87  tff(c_204, plain, (k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_1'))=k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_202])).
% 3.51/1.87  tff(c_210, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_162, c_204])).
% 3.51/1.87  tff(c_216, plain, (![B_71, A_72, C_73]: (k8_relset_1(B_71, A_72, C_73, k7_relset_1(B_71, A_72, C_73, B_71))=k1_relset_1(B_71, A_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.51/1.87  tff(c_218, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_1')))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_216])).
% 3.51/1.87  tff(c_224, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_176, c_145, c_218])).
% 3.51/1.87  tff(c_248, plain, (![B_89, A_90, C_91]: (k1_xboole_0=B_89 | k8_relset_1(A_90, B_89, C_91, k7_relset_1(A_90, B_89, C_91, A_90))=A_90 | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(C_91, A_90, B_89) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.51/1.87  tff(c_250, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_248])).
% 3.51/1.87  tff(c_257, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_123, c_224, c_210, c_176, c_250])).
% 3.51/1.87  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_93, c_257])).
% 3.51/1.87  tff(c_261, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.51/1.87  tff(c_270, plain, (![A_92]: (u1_struct_0(A_92)=k2_struct_0(A_92) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.51/1.87  tff(c_273, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_270])).
% 3.51/1.87  tff(c_278, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273])).
% 3.51/1.87  tff(c_302, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_278, c_42])).
% 3.51/1.87  tff(c_304, plain, (![A_95, B_96]: (k9_relat_1(k6_relat_1(A_95), B_96)=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.87  tff(c_307, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_302, c_304])).
% 3.51/1.87  tff(c_309, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_307])).
% 3.51/1.87  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.51/1.87  tff(c_322, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_12])).
% 3.51/1.87  tff(c_311, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_302])).
% 3.51/1.87  tff(c_362, plain, (![A_100]: (k2_zfmisc_1(A_100, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_4])).
% 3.51/1.87  tff(c_18, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.87  tff(c_421, plain, (![A_112, C_113]: (k1_relset_1(A_112, '#skF_3', C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_362, c_18])).
% 3.51/1.87  tff(c_423, plain, (![A_112]: (k1_relset_1(A_112, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_311, c_421])).
% 3.51/1.87  tff(c_425, plain, (![A_112]: (k1_relset_1(A_112, '#skF_3', '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_423])).
% 3.51/1.87  tff(c_320, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_4])).
% 3.51/1.87  tff(c_490, plain, (![A_127, B_128, C_129]: (k8_relset_1(A_127, B_128, C_129, B_128)=k1_relset_1(A_127, B_128, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.51/1.87  tff(c_527, plain, (![A_140, C_141]: (k8_relset_1(A_140, '#skF_3', C_141, '#skF_3')=k1_relset_1(A_140, '#skF_3', C_141) | ~m1_subset_1(C_141, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_320, c_490])).
% 3.51/1.87  tff(c_529, plain, (![A_140]: (k8_relset_1(A_140, '#skF_3', '#skF_3', '#skF_3')=k1_relset_1(A_140, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_311, c_527])).
% 3.51/1.87  tff(c_531, plain, (![A_140]: (k8_relset_1(A_140, '#skF_3', '#skF_3', '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_529])).
% 3.51/1.87  tff(c_260, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.51/1.87  tff(c_276, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_270])).
% 3.51/1.87  tff(c_280, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_276])).
% 3.51/1.87  tff(c_303, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_280, c_278, c_261, c_260, c_38])).
% 3.51/1.87  tff(c_310, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_309, c_309, c_303])).
% 3.51/1.87  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_531, c_310])).
% 3.51/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.87  
% 3.51/1.87  Inference rules
% 3.51/1.87  ----------------------
% 3.51/1.87  #Ref     : 0
% 3.51/1.87  #Sup     : 140
% 3.51/1.87  #Fact    : 0
% 3.51/1.87  #Define  : 0
% 3.51/1.87  #Split   : 1
% 3.51/1.87  #Chain   : 0
% 3.51/1.87  #Close   : 0
% 3.51/1.87  
% 3.51/1.87  Ordering : KBO
% 3.51/1.87  
% 3.51/1.87  Simplification rules
% 3.51/1.87  ----------------------
% 3.51/1.87  #Subsume      : 0
% 3.51/1.87  #Demod        : 70
% 3.51/1.87  #Tautology    : 91
% 3.51/1.87  #SimpNegUnit  : 1
% 3.51/1.87  #BackRed      : 18
% 3.51/1.87  
% 3.51/1.87  #Partial instantiations: 0
% 3.51/1.87  #Strategies tried      : 1
% 3.51/1.87  
% 3.51/1.87  Timing (in seconds)
% 3.51/1.87  ----------------------
% 3.51/1.87  Preprocessing        : 0.55
% 3.51/1.87  Parsing              : 0.29
% 3.51/1.87  CNF conversion       : 0.04
% 3.51/1.87  Main loop            : 0.46
% 3.51/1.87  Inferencing          : 0.16
% 3.51/1.87  Reduction            : 0.15
% 3.51/1.87  Demodulation         : 0.11
% 3.51/1.87  BG Simplification    : 0.03
% 3.51/1.87  Subsumption          : 0.07
% 3.51/1.87  Abstraction          : 0.02
% 3.51/1.87  MUC search           : 0.00
% 3.51/1.87  Cooper               : 0.00
% 3.51/1.87  Total                : 1.08
% 3.51/1.87  Index Insertion      : 0.00
% 3.51/1.87  Index Deletion       : 0.00
% 3.51/1.87  Index Matching       : 0.00
% 3.51/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
