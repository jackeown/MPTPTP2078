%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 589 expanded)
%              Number of leaves         :   46 ( 218 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 (1324 expanded)
%              Number of equality atoms :   75 ( 597 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_93,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_137,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(c_16,plain,(
    ! [A_9] : k10_relat_1(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2097,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k8_relset_1(A_241,B_242,C_243,D_244) = k10_relat_1(C_243,D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2100,plain,(
    ! [A_241,B_242,D_244] : k8_relset_1(A_241,B_242,k1_xboole_0,D_244) = k10_relat_1(k1_xboole_0,D_244) ),
    inference(resolution,[status(thm)],[c_8,c_2097])).

tff(c_2108,plain,(
    ! [A_245,B_246,D_247] : k8_relset_1(A_245,B_246,k1_xboole_0,D_247) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2100])).

tff(c_1305,plain,(
    ! [A_165] : k6_relat_1(A_165) = k6_partfun1(A_165) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1311,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_26])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_166,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_174,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_166])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_173,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_166])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_203,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_173,c_58])).

tff(c_32,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_207,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_32])).

tff(c_219,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_233,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_203,c_219])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( k5_relat_1(B_15,k6_relat_1(A_14)) = B_15
      | ~ r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_349,plain,(
    ! [B_86,A_87] :
      ( k5_relat_1(B_86,k6_partfun1(A_87)) = B_86
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24])).

tff(c_359,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_partfun1(A_7)) = B_8
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_349])).

tff(c_28,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [A_16] : v1_relat_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_952,plain,(
    ! [A_135,B_136] :
      ( k10_relat_1(A_135,k1_relat_1(B_136)) = k1_relat_1(k5_relat_1(A_135,B_136))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_972,plain,(
    ! [A_135,A_13] :
      ( k1_relat_1(k5_relat_1(A_135,k6_partfun1(A_13))) = k10_relat_1(A_135,A_13)
      | ~ v1_relat_1(k6_partfun1(A_13))
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_952])).

tff(c_1066,plain,(
    ! [A_142,A_143] :
      ( k1_relat_1(k5_relat_1(A_142,k6_partfun1(A_143))) = k10_relat_1(A_142,A_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_972])).

tff(c_1139,plain,(
    ! [B_146,A_147] :
      ( k10_relat_1(B_146,A_147) = k1_relat_1(B_146)
      | ~ v1_relat_1(B_146)
      | ~ v5_relat_1(B_146,A_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1066])).

tff(c_1145,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_1139])).

tff(c_1154,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_1145])).

tff(c_292,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_306,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_203,c_292])).

tff(c_402,plain,(
    ! [B_91,A_92] :
      ( k1_relat_1(B_91) = A_92
      | ~ v1_partfun1(B_91,A_92)
      | ~ v4_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_405,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_306,c_402])).

tff(c_411,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_405])).

tff(c_421,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_56,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_102,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_175,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60])).

tff(c_195,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_175])).

tff(c_804,plain,(
    ! [B_124,C_125,A_126] :
      ( k1_xboole_0 = B_124
      | v1_partfun1(C_125,A_126)
      | ~ v1_funct_2(C_125,A_126,B_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_807,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_804])).

tff(c_820,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_195,c_807])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_102,c_820])).

tff(c_823,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_828,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_203])).

tff(c_1222,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k8_relset_1(A_150,B_151,C_152,D_153) = k10_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1232,plain,(
    ! [D_153] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_153) = k10_relat_1('#skF_3',D_153) ),
    inference(resolution,[status(thm)],[c_828,c_1222])).

tff(c_54,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_265,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_173,c_54])).

tff(c_827,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_823,c_265])).

tff(c_1266,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_827])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_1266])).

tff(c_1271,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1343,plain,(
    ! [A_166] :
      ( u1_struct_0(A_166) = k2_struct_0(A_166)
      | ~ l1_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1346,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1343])).

tff(c_1351,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_1346])).

tff(c_1354,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1351,c_58])).

tff(c_1356,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1354])).

tff(c_1543,plain,(
    ! [A_206,B_207] :
      ( k8_relset_1(A_206,A_206,k6_partfun1(A_206),B_207) = B_207
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1545,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1356,c_1543])).

tff(c_1549,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1545])).

tff(c_2112,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_1549])).

tff(c_1270,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1349,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1343])).

tff(c_1353,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1349])).

tff(c_1377,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1351,c_1271,c_1270,c_54])).

tff(c_2147,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_2112,c_2112,c_2112,c_1377])).

tff(c_2156,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_2112,c_1311])).

tff(c_2149,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_1356])).

tff(c_50,plain,(
    ! [A_33,B_34] :
      ( k8_relset_1(A_33,A_33,k6_partfun1(A_33),B_34) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2293,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2149,c_50])).

tff(c_2298,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_2293])).

tff(c_2300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2147,c_2298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.62  
% 3.66/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.63  
% 3.66/1.63  %Foreground sorts:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Background operators:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Foreground operators:
% 3.66/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.63  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.66/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.66/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.66/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.66/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.66/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.63  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.66/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.63  
% 4.01/1.65  tff(f_47, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 4.01/1.65  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.01/1.65  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.01/1.65  tff(f_93, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.01/1.65  tff(f_65, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.01/1.65  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.01/1.65  tff(f_137, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 4.01/1.65  tff(f_118, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.01/1.65  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.01/1.65  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.01/1.65  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.01/1.65  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.01/1.65  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.01/1.65  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.01/1.65  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.01/1.65  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.01/1.65  tff(f_110, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 4.01/1.65  tff(f_114, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 4.01/1.65  tff(c_16, plain, (![A_9]: (k10_relat_1(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.65  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.01/1.65  tff(c_2097, plain, (![A_241, B_242, C_243, D_244]: (k8_relset_1(A_241, B_242, C_243, D_244)=k10_relat_1(C_243, D_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.65  tff(c_2100, plain, (![A_241, B_242, D_244]: (k8_relset_1(A_241, B_242, k1_xboole_0, D_244)=k10_relat_1(k1_xboole_0, D_244))), inference(resolution, [status(thm)], [c_8, c_2097])).
% 4.01/1.65  tff(c_2108, plain, (![A_245, B_246, D_247]: (k8_relset_1(A_245, B_246, k1_xboole_0, D_247)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2100])).
% 4.01/1.65  tff(c_1305, plain, (![A_165]: (k6_relat_1(A_165)=k6_partfun1(A_165))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.65  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.65  tff(c_1311, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1305, c_26])).
% 4.01/1.65  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.65  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_166, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.01/1.65  tff(c_174, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_166])).
% 4.01/1.65  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_173, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_166])).
% 4.01/1.65  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_203, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_173, c_58])).
% 4.01/1.65  tff(c_32, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.65  tff(c_207, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_203, c_32])).
% 4.01/1.65  tff(c_219, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.01/1.65  tff(c_233, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_203, c_219])).
% 4.01/1.65  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.65  tff(c_44, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.65  tff(c_24, plain, (![B_15, A_14]: (k5_relat_1(B_15, k6_relat_1(A_14))=B_15 | ~r1_tarski(k2_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.01/1.65  tff(c_349, plain, (![B_86, A_87]: (k5_relat_1(B_86, k6_partfun1(A_87))=B_86 | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24])).
% 4.01/1.65  tff(c_359, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_partfun1(A_7))=B_8 | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_14, c_349])).
% 4.01/1.65  tff(c_28, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.01/1.65  tff(c_68, plain, (![A_16]: (v1_relat_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 4.01/1.65  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.65  tff(c_71, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 4.01/1.65  tff(c_952, plain, (![A_135, B_136]: (k10_relat_1(A_135, k1_relat_1(B_136))=k1_relat_1(k5_relat_1(A_135, B_136)) | ~v1_relat_1(B_136) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.01/1.65  tff(c_972, plain, (![A_135, A_13]: (k1_relat_1(k5_relat_1(A_135, k6_partfun1(A_13)))=k10_relat_1(A_135, A_13) | ~v1_relat_1(k6_partfun1(A_13)) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_71, c_952])).
% 4.01/1.65  tff(c_1066, plain, (![A_142, A_143]: (k1_relat_1(k5_relat_1(A_142, k6_partfun1(A_143)))=k10_relat_1(A_142, A_143) | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_972])).
% 4.01/1.65  tff(c_1139, plain, (![B_146, A_147]: (k10_relat_1(B_146, A_147)=k1_relat_1(B_146) | ~v1_relat_1(B_146) | ~v5_relat_1(B_146, A_147) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1066])).
% 4.01/1.65  tff(c_1145, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_233, c_1139])).
% 4.01/1.65  tff(c_1154, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_1145])).
% 4.01/1.65  tff(c_292, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.01/1.65  tff(c_306, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_203, c_292])).
% 4.01/1.65  tff(c_402, plain, (![B_91, A_92]: (k1_relat_1(B_91)=A_92 | ~v1_partfun1(B_91, A_92) | ~v4_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.01/1.65  tff(c_405, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_306, c_402])).
% 4.01/1.65  tff(c_411, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_405])).
% 4.01/1.65  tff(c_421, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_411])).
% 4.01/1.65  tff(c_56, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_102, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 4.01/1.65  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_175, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60])).
% 4.01/1.65  tff(c_195, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_175])).
% 4.01/1.65  tff(c_804, plain, (![B_124, C_125, A_126]: (k1_xboole_0=B_124 | v1_partfun1(C_125, A_126) | ~v1_funct_2(C_125, A_126, B_124) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_1(C_125))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.01/1.65  tff(c_807, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_203, c_804])).
% 4.01/1.65  tff(c_820, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_195, c_807])).
% 4.01/1.65  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_102, c_820])).
% 4.01/1.65  tff(c_823, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_411])).
% 4.01/1.65  tff(c_828, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_823, c_203])).
% 4.01/1.65  tff(c_1222, plain, (![A_150, B_151, C_152, D_153]: (k8_relset_1(A_150, B_151, C_152, D_153)=k10_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.65  tff(c_1232, plain, (![D_153]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_153)=k10_relat_1('#skF_3', D_153))), inference(resolution, [status(thm)], [c_828, c_1222])).
% 4.01/1.65  tff(c_54, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.01/1.65  tff(c_265, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_173, c_54])).
% 4.01/1.65  tff(c_827, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_823, c_265])).
% 4.01/1.65  tff(c_1266, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_827])).
% 4.01/1.65  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1154, c_1266])).
% 4.01/1.65  tff(c_1271, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 4.01/1.65  tff(c_1343, plain, (![A_166]: (u1_struct_0(A_166)=k2_struct_0(A_166) | ~l1_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.01/1.65  tff(c_1346, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1343])).
% 4.01/1.65  tff(c_1351, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_1346])).
% 4.01/1.65  tff(c_1354, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1351, c_58])).
% 4.01/1.65  tff(c_1356, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1354])).
% 4.01/1.65  tff(c_1543, plain, (![A_206, B_207]: (k8_relset_1(A_206, A_206, k6_partfun1(A_206), B_207)=B_207 | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.01/1.65  tff(c_1545, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1356, c_1543])).
% 4.01/1.65  tff(c_1549, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1545])).
% 4.01/1.65  tff(c_2112, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2108, c_1549])).
% 4.01/1.65  tff(c_1270, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 4.01/1.65  tff(c_1349, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_1343])).
% 4.01/1.65  tff(c_1353, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1349])).
% 4.01/1.65  tff(c_1377, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1351, c_1271, c_1270, c_54])).
% 4.01/1.65  tff(c_2147, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_2112, c_2112, c_2112, c_1377])).
% 4.01/1.65  tff(c_2156, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_2112, c_1311])).
% 4.01/1.65  tff(c_2149, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_1356])).
% 4.01/1.65  tff(c_50, plain, (![A_33, B_34]: (k8_relset_1(A_33, A_33, k6_partfun1(A_33), B_34)=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.01/1.65  tff(c_2293, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2149, c_50])).
% 4.01/1.65  tff(c_2298, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_2293])).
% 4.01/1.65  tff(c_2300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2147, c_2298])).
% 4.01/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.65  
% 4.01/1.65  Inference rules
% 4.01/1.65  ----------------------
% 4.01/1.65  #Ref     : 0
% 4.01/1.65  #Sup     : 496
% 4.01/1.65  #Fact    : 0
% 4.01/1.65  #Define  : 0
% 4.01/1.65  #Split   : 2
% 4.01/1.65  #Chain   : 0
% 4.01/1.65  #Close   : 0
% 4.01/1.65  
% 4.01/1.65  Ordering : KBO
% 4.01/1.65  
% 4.01/1.65  Simplification rules
% 4.01/1.65  ----------------------
% 4.01/1.65  #Subsume      : 39
% 4.01/1.65  #Demod        : 504
% 4.01/1.65  #Tautology    : 316
% 4.01/1.65  #SimpNegUnit  : 3
% 4.01/1.65  #BackRed      : 60
% 4.01/1.65  
% 4.01/1.65  #Partial instantiations: 0
% 4.01/1.65  #Strategies tried      : 1
% 4.01/1.65  
% 4.01/1.65  Timing (in seconds)
% 4.01/1.65  ----------------------
% 4.01/1.65  Preprocessing        : 0.33
% 4.01/1.65  Parsing              : 0.18
% 4.01/1.65  CNF conversion       : 0.02
% 4.01/1.65  Main loop            : 0.55
% 4.01/1.65  Inferencing          : 0.20
% 4.01/1.65  Reduction            : 0.20
% 4.01/1.65  Demodulation         : 0.14
% 4.01/1.65  BG Simplification    : 0.02
% 4.01/1.65  Subsumption          : 0.08
% 4.01/1.65  Abstraction          : 0.03
% 4.01/1.65  MUC search           : 0.00
% 4.01/1.65  Cooper               : 0.00
% 4.01/1.65  Total                : 0.94
% 4.01/1.65  Index Insertion      : 0.00
% 4.01/1.65  Index Deletion       : 0.00
% 4.01/1.65  Index Matching       : 0.00
% 4.01/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
