%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 550 expanded)
%              Number of leaves         :   33 ( 201 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 (1464 expanded)
%              Number of equality atoms :   46 ( 571 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_36,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_47,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_59,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_30])).

tff(c_61,plain,(
    ! [B_28,A_29] :
      ( v1_relat_1(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_59,c_61])).

tff(c_67,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_68,plain,(
    ! [C_30,A_31,B_32] :
      ( v4_relat_1(C_30,A_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_59,c_68])).

tff(c_80,plain,(
    ! [B_37,A_38] :
      ( k1_relat_1(B_37) = A_38
      | ~ v1_partfun1(B_37,A_38)
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_83,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_80])).

tff(c_86,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_83])).

tff(c_87,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_28,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_32])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_49])).

tff(c_116,plain,(
    ! [B_50,C_51,A_52] :
      ( k1_xboole_0 = B_50
      | v1_partfun1(C_51,A_52)
      | ~ v1_funct_2(C_51,A_52,B_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_119,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_116])).

tff(c_122,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60,c_119])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_58,c_122])).

tff(c_125,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_78,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_26])).

tff(c_127,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_78])).

tff(c_130,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_59])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_167,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_10])).

tff(c_188,plain,(
    ! [A_61,B_62,C_63] :
      ( k8_relset_1(A_61,B_62,C_63,B_62) = k1_relset_1(A_61,B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_190,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_188])).

tff(c_192,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_190])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_192])).

tff(c_196,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_202,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_47])).

tff(c_195,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_197,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_48])).

tff(c_235,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_197,c_196,c_195,c_26])).

tff(c_215,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_197,c_30])).

tff(c_217,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_220,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_215,c_217])).

tff(c_223,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_220])).

tff(c_229,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_233,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_215,c_229])).

tff(c_236,plain,(
    ! [B_73,A_74] :
      ( k1_relat_1(B_73) = A_74
      | ~ v1_partfun1(B_73,A_74)
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_239,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_236])).

tff(c_242,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_239])).

tff(c_243,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_216,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_196,c_49])).

tff(c_258,plain,(
    ! [C_81,B_82] :
      ( v1_partfun1(C_81,k1_xboole_0)
      | ~ v1_funct_2(C_81,k1_xboole_0,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_82)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_258])).

tff(c_264,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_216,c_261])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_264])).

tff(c_267,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_279,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_282,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_279])).

tff(c_284,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_282])).

tff(c_304,plain,(
    ! [A_91,B_92,C_93] :
      ( k8_relset_1(A_91,B_92,C_93,B_92) = k1_relset_1(A_91,B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_306,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_304])).

tff(c_308,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_306])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.29  
% 2.27/1.29  %Foreground sorts:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Background operators:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Foreground operators:
% 2.27/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.27/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.27/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.29  
% 2.27/1.31  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.31  tff(f_98, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 2.27/1.31  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.27/1.31  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.31  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.31  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.27/1.31  tff(f_75, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.27/1.31  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.31  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.27/1.31  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.31  tff(c_38, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_40, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.31  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_40])).
% 2.27/1.31  tff(c_36, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_47, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_40])).
% 2.27/1.31  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_59, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_30])).
% 2.27/1.31  tff(c_61, plain, (![B_28, A_29]: (v1_relat_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.31  tff(c_64, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_59, c_61])).
% 2.27/1.31  tff(c_67, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.27/1.31  tff(c_68, plain, (![C_30, A_31, B_32]: (v4_relat_1(C_30, A_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.31  tff(c_72, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_59, c_68])).
% 2.27/1.31  tff(c_80, plain, (![B_37, A_38]: (k1_relat_1(B_37)=A_38 | ~v1_partfun1(B_37, A_38) | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.31  tff(c_83, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_80])).
% 2.27/1.31  tff(c_86, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_83])).
% 2.27/1.31  tff(c_87, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_86])).
% 2.27/1.31  tff(c_28, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_58, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.27/1.31  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_32, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_49, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_32])).
% 2.27/1.31  tff(c_60, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_49])).
% 2.27/1.31  tff(c_116, plain, (![B_50, C_51, A_52]: (k1_xboole_0=B_50 | v1_partfun1(C_51, A_52) | ~v1_funct_2(C_51, A_52, B_50) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_50))) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.31  tff(c_119, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_116])).
% 2.27/1.31  tff(c_122, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_60, c_119])).
% 2.27/1.31  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_58, c_122])).
% 2.27/1.31  tff(c_125, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 2.27/1.31  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_78, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_26])).
% 2.27/1.31  tff(c_127, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_78])).
% 2.27/1.31  tff(c_130, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_59])).
% 2.27/1.31  tff(c_10, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.31  tff(c_167, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_10])).
% 2.27/1.31  tff(c_188, plain, (![A_61, B_62, C_63]: (k8_relset_1(A_61, B_62, C_63, B_62)=k1_relset_1(A_61, B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.31  tff(c_190, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_130, c_188])).
% 2.27/1.31  tff(c_192, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_190])).
% 2.27/1.31  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_192])).
% 2.27/1.31  tff(c_196, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.27/1.31  tff(c_202, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_196, c_47])).
% 2.27/1.31  tff(c_195, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.27/1.31  tff(c_197, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_195, c_48])).
% 2.27/1.31  tff(c_235, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_197, c_196, c_195, c_26])).
% 2.27/1.31  tff(c_215, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_197, c_30])).
% 2.27/1.31  tff(c_217, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.31  tff(c_220, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_215, c_217])).
% 2.27/1.31  tff(c_223, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_220])).
% 2.27/1.31  tff(c_229, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.31  tff(c_233, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_215, c_229])).
% 2.27/1.31  tff(c_236, plain, (![B_73, A_74]: (k1_relat_1(B_73)=A_74 | ~v1_partfun1(B_73, A_74) | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.31  tff(c_239, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_233, c_236])).
% 2.27/1.31  tff(c_242, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_239])).
% 2.27/1.31  tff(c_243, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_242])).
% 2.27/1.31  tff(c_216, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_196, c_49])).
% 2.27/1.31  tff(c_258, plain, (![C_81, B_82]: (v1_partfun1(C_81, k1_xboole_0) | ~v1_funct_2(C_81, k1_xboole_0, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_82))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.31  tff(c_261, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_215, c_258])).
% 2.27/1.31  tff(c_264, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_216, c_261])).
% 2.27/1.31  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_264])).
% 2.27/1.31  tff(c_267, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 2.27/1.31  tff(c_279, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.31  tff(c_282, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_215, c_279])).
% 2.27/1.31  tff(c_284, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_267, c_282])).
% 2.27/1.31  tff(c_304, plain, (![A_91, B_92, C_93]: (k8_relset_1(A_91, B_92, C_93, B_92)=k1_relset_1(A_91, B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.31  tff(c_306, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_215, c_304])).
% 2.27/1.31  tff(c_308, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_284, c_306])).
% 2.27/1.31  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_308])).
% 2.27/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  Inference rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Ref     : 0
% 2.27/1.31  #Sup     : 64
% 2.27/1.31  #Fact    : 0
% 2.27/1.31  #Define  : 0
% 2.27/1.31  #Split   : 3
% 2.27/1.31  #Chain   : 0
% 2.27/1.31  #Close   : 0
% 2.27/1.31  
% 2.27/1.31  Ordering : KBO
% 2.27/1.31  
% 2.27/1.31  Simplification rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Subsume      : 0
% 2.27/1.31  #Demod        : 52
% 2.27/1.31  #Tautology    : 41
% 2.27/1.31  #SimpNegUnit  : 4
% 2.27/1.31  #BackRed      : 9
% 2.27/1.31  
% 2.27/1.31  #Partial instantiations: 0
% 2.27/1.31  #Strategies tried      : 1
% 2.27/1.31  
% 2.27/1.31  Timing (in seconds)
% 2.27/1.31  ----------------------
% 2.27/1.31  Preprocessing        : 0.31
% 2.27/1.31  Parsing              : 0.16
% 2.27/1.31  CNF conversion       : 0.02
% 2.27/1.31  Main loop            : 0.20
% 2.27/1.31  Inferencing          : 0.07
% 2.27/1.31  Reduction            : 0.07
% 2.27/1.31  Demodulation         : 0.05
% 2.27/1.31  BG Simplification    : 0.01
% 2.27/1.31  Subsumption          : 0.02
% 2.27/1.31  Abstraction          : 0.01
% 2.27/1.31  MUC search           : 0.00
% 2.27/1.31  Cooper               : 0.00
% 2.27/1.31  Total                : 0.55
% 2.27/1.31  Index Insertion      : 0.00
% 2.27/1.31  Index Deletion       : 0.00
% 2.27/1.31  Index Matching       : 0.00
% 2.27/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
