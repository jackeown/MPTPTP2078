%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 622 expanded)
%              Number of leaves         :   35 ( 221 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 (1657 expanded)
%              Number of equality atoms :   45 ( 649 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_30,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_40,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_42])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_49,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49,c_32])).

tff(c_63,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_63])).

tff(c_68,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_61,c_68])).

tff(c_86,plain,(
    ! [B_44,A_45] :
      ( k1_relat_1(B_44) = A_45
      | ~ v1_partfun1(B_44,A_45)
      | ~ v4_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_89,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_86])).

tff(c_92,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_89])).

tff(c_93,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_51,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_34])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_51])).

tff(c_121,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_partfun1(C_55,A_56)
      | ~ v1_funct_2(C_55,A_56,B_57)
      | ~ v1_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_61,c_121])).

tff(c_127,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_124])).

tff(c_128,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_127])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_131])).

tff(c_136,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49,c_28])).

tff(c_144,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_136,c_78])).

tff(c_138,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_138])).

tff(c_172,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_142])).

tff(c_147,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_61])).

tff(c_202,plain,(
    ! [A_61,B_62,C_63] :
      ( k8_relset_1(A_61,B_62,C_63,B_62) = k1_relset_1(A_61,B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_204,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_202])).

tff(c_206,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_204])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_206])).

tff(c_209,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_217,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_49])).

tff(c_208,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_210,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_50])).

tff(c_242,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_210,c_209,c_208,c_28])).

tff(c_215,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32])).

tff(c_216,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_215])).

tff(c_231,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_216])).

tff(c_232,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_236,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_232])).

tff(c_243,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_231,c_243])).

tff(c_249,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(B_74) = A_75
      | ~ v1_partfun1(B_74,A_75)
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_252,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_247,c_249])).

tff(c_255,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_252])).

tff(c_256,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_257,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_partfun1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_261,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_231,c_257])).

tff(c_262,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_261])).

tff(c_230,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_209,c_51])).

tff(c_290,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_partfun1(C_88,A_89)
      | ~ v1_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | v1_xboole_0(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_293,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_231,c_290])).

tff(c_296,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_230,c_293])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_256,c_296])).

tff(c_299,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_317,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_320,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_317])).

tff(c_322,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_320])).

tff(c_335,plain,(
    ! [A_100,B_101,C_102] :
      ( k8_relset_1(A_100,B_101,C_102,B_101) = k1_relset_1(A_100,B_101,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_337,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_335])).

tff(c_339,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_337])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.33  
% 2.21/1.33  %Foreground sorts:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Background operators:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Foreground operators:
% 2.21/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.21/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.21/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.21/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.33  
% 2.62/1.35  tff(f_101, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 2.62/1.35  tff(f_82, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.62/1.35  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.35  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.35  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.62/1.35  tff(f_70, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.62/1.35  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.35  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.35  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.62/1.35  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.62/1.35  tff(c_30, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_60, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.62/1.35  tff(c_40, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_42, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.62/1.35  tff(c_50, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_42])).
% 2.62/1.35  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_49, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_42])).
% 2.62/1.35  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_61, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_49, c_32])).
% 2.62/1.35  tff(c_63, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.35  tff(c_67, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_63])).
% 2.62/1.35  tff(c_68, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.35  tff(c_72, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_68])).
% 2.62/1.35  tff(c_86, plain, (![B_44, A_45]: (k1_relat_1(B_44)=A_45 | ~v1_partfun1(B_44, A_45) | ~v4_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.35  tff(c_89, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_86])).
% 2.62/1.35  tff(c_92, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_89])).
% 2.62/1.35  tff(c_93, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.62/1.35  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_51, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_34])).
% 2.62/1.35  tff(c_62, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_51])).
% 2.62/1.35  tff(c_121, plain, (![C_55, A_56, B_57]: (v1_partfun1(C_55, A_56) | ~v1_funct_2(C_55, A_56, B_57) | ~v1_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.62/1.35  tff(c_124, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_61, c_121])).
% 2.62/1.35  tff(c_127, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_124])).
% 2.62/1.35  tff(c_128, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_93, c_127])).
% 2.62/1.35  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.35  tff(c_131, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_2])).
% 2.62/1.35  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_131])).
% 2.62/1.35  tff(c_136, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 2.62/1.35  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.35  tff(c_78, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_49, c_28])).
% 2.62/1.35  tff(c_144, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_136, c_78])).
% 2.62/1.35  tff(c_138, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_142, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_138])).
% 2.62/1.35  tff(c_172, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_142])).
% 2.62/1.35  tff(c_147, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_61])).
% 2.62/1.35  tff(c_202, plain, (![A_61, B_62, C_63]: (k8_relset_1(A_61, B_62, C_63, B_62)=k1_relset_1(A_61, B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.35  tff(c_204, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_147, c_202])).
% 2.62/1.35  tff(c_206, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_204])).
% 2.62/1.35  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_206])).
% 2.62/1.35  tff(c_209, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.35  tff(c_217, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_49])).
% 2.62/1.35  tff(c_208, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.35  tff(c_210, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_208, c_50])).
% 2.62/1.35  tff(c_242, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_210, c_209, c_208, c_28])).
% 2.62/1.35  tff(c_215, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32])).
% 2.62/1.35  tff(c_216, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_215])).
% 2.62/1.35  tff(c_231, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_216])).
% 2.62/1.35  tff(c_232, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.35  tff(c_236, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_232])).
% 2.62/1.35  tff(c_243, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.35  tff(c_247, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_243])).
% 2.62/1.35  tff(c_249, plain, (![B_74, A_75]: (k1_relat_1(B_74)=A_75 | ~v1_partfun1(B_74, A_75) | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.35  tff(c_252, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_247, c_249])).
% 2.62/1.35  tff(c_255, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_252])).
% 2.62/1.35  tff(c_256, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_255])).
% 2.62/1.35  tff(c_257, plain, (![C_76, A_77, B_78]: (v1_partfun1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.35  tff(c_261, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_257])).
% 2.62/1.35  tff(c_262, plain, (~v1_xboole_0(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_256, c_261])).
% 2.62/1.35  tff(c_230, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_209, c_51])).
% 2.62/1.35  tff(c_290, plain, (![C_88, A_89, B_90]: (v1_partfun1(C_88, A_89) | ~v1_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | v1_xboole_0(B_90))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.62/1.35  tff(c_293, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_290])).
% 2.62/1.35  tff(c_296, plain, (v1_partfun1('#skF_3', k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_230, c_293])).
% 2.62/1.35  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_256, c_296])).
% 2.62/1.35  tff(c_299, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_255])).
% 2.62/1.35  tff(c_317, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_320, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_317])).
% 2.62/1.35  tff(c_322, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_299, c_320])).
% 2.62/1.35  tff(c_335, plain, (![A_100, B_101, C_102]: (k8_relset_1(A_100, B_101, C_102, B_101)=k1_relset_1(A_100, B_101, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.35  tff(c_337, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_231, c_335])).
% 2.62/1.35  tff(c_339, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_322, c_337])).
% 2.62/1.35  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_339])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 71
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 4
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 1
% 2.62/1.35  #Demod        : 52
% 2.62/1.35  #Tautology    : 45
% 2.62/1.35  #SimpNegUnit  : 6
% 2.62/1.35  #BackRed      : 12
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.36  Preprocessing        : 0.35
% 2.62/1.36  Parsing              : 0.18
% 2.62/1.36  CNF conversion       : 0.02
% 2.62/1.36  Main loop            : 0.24
% 2.62/1.36  Inferencing          : 0.08
% 2.62/1.36  Reduction            : 0.08
% 2.62/1.36  Demodulation         : 0.06
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.03
% 2.62/1.36  Abstraction          : 0.02
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.63
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
