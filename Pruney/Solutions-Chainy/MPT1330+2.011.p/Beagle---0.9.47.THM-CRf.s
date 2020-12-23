%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 517 expanded)
%              Number of leaves         :   40 ( 189 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 (1299 expanded)
%              Number of equality atoms :   48 ( 488 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_106,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_36,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_49,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_50])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_59,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_38])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_59])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_10])).

tff(c_81,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_71,c_81])).

tff(c_108,plain,(
    ! [B_50,A_51] :
      ( k1_relat_1(B_50) = A_51
      | ~ v1_partfun1(B_50,A_51)
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_111,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_108])).

tff(c_114,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_111])).

tff(c_115,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40])).

tff(c_69,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60])).

tff(c_157,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_157])).

tff(c_163,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_69,c_160])).

tff(c_164,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_163])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_167,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_167])).

tff(c_172,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_176,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_71])).

tff(c_225,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k8_relset_1(A_72,B_73,C_74,D_75) = k10_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [D_75] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_75) = k10_relat_1('#skF_3',D_75) ),
    inference(resolution,[status(thm)],[c_176,c_225])).

tff(c_34,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_86,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_34])).

tff(c_175,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_86])).

tff(c_229,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_175])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_16])).

tff(c_247,plain,(
    ! [A_80,B_81,C_82] :
      ( k8_relset_1(A_80,B_81,C_82,B_81) = k1_relset_1(A_80,B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_249,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_247])).

tff(c_251,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_214,c_249])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_251])).

tff(c_254,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_264,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_270,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_264])).

tff(c_274,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_270])).

tff(c_255,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_267,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_264])).

tff(c_272,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_267])).

tff(c_275,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_38])).

tff(c_286,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_275])).

tff(c_287,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_291,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_287])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_304,plain,(
    ! [B_94,A_95] :
      ( k10_relat_1(B_94,A_95) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_94),A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [B_96] :
      ( k10_relat_1(B_96,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_314,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_291,c_310])).

tff(c_341,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k8_relset_1(A_104,B_105,C_106,D_107) = k10_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_344,plain,(
    ! [D_107] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',D_107) = k10_relat_1('#skF_3',D_107) ),
    inference(resolution,[status(thm)],[c_286,c_341])).

tff(c_302,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_272,c_255,c_254,c_34])).

tff(c_345,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_302])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.42  
% 2.45/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.42  
% 2.45/1.42  %Foreground sorts:
% 2.45/1.42  
% 2.45/1.42  
% 2.45/1.42  %Background operators:
% 2.45/1.42  
% 2.45/1.42  
% 2.45/1.42  %Foreground operators:
% 2.45/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.45/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.45/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.45/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.45/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.45/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.42  
% 2.45/1.44  tff(f_106, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 2.45/1.44  tff(f_87, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.45/1.44  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.44  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.44  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.45/1.44  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.45/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.45/1.44  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.45/1.44  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.45/1.44  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.45/1.44  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.44  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.45/1.44  tff(c_36, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_49, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.45/1.44  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_50, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.45/1.44  tff(c_58, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_50])).
% 2.45/1.44  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_50])).
% 2.45/1.44  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_59, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_38])).
% 2.45/1.44  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_59])).
% 2.45/1.44  tff(c_10, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.44  tff(c_75, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_10])).
% 2.45/1.44  tff(c_81, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.45/1.44  tff(c_85, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_71, c_81])).
% 2.45/1.44  tff(c_108, plain, (![B_50, A_51]: (k1_relat_1(B_50)=A_51 | ~v1_partfun1(B_50, A_51) | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.45/1.44  tff(c_111, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_108])).
% 2.45/1.44  tff(c_114, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_111])).
% 2.45/1.44  tff(c_115, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.45/1.44  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40])).
% 2.45/1.44  tff(c_69, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60])).
% 2.45/1.44  tff(c_157, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.45/1.44  tff(c_160, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_71, c_157])).
% 2.45/1.44  tff(c_163, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_69, c_160])).
% 2.45/1.44  tff(c_164, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_115, c_163])).
% 2.45/1.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.44  tff(c_167, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_2])).
% 2.45/1.44  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_167])).
% 2.45/1.44  tff(c_172, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_114])).
% 2.45/1.44  tff(c_176, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_71])).
% 2.45/1.44  tff(c_225, plain, (![A_72, B_73, C_74, D_75]: (k8_relset_1(A_72, B_73, C_74, D_75)=k10_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.44  tff(c_228, plain, (![D_75]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_75)=k10_relat_1('#skF_3', D_75))), inference(resolution, [status(thm)], [c_176, c_225])).
% 2.45/1.44  tff(c_34, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.44  tff(c_86, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_34])).
% 2.45/1.44  tff(c_175, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_86])).
% 2.45/1.44  tff(c_229, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_175])).
% 2.45/1.44  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.44  tff(c_214, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_16])).
% 2.45/1.44  tff(c_247, plain, (![A_80, B_81, C_82]: (k8_relset_1(A_80, B_81, C_82, B_81)=k1_relset_1(A_80, B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.44  tff(c_249, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_176, c_247])).
% 2.45/1.44  tff(c_251, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_214, c_249])).
% 2.45/1.44  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_251])).
% 2.45/1.44  tff(c_254, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.45/1.44  tff(c_264, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.45/1.44  tff(c_270, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_264])).
% 2.45/1.44  tff(c_274, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_254, c_270])).
% 2.45/1.44  tff(c_255, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.45/1.44  tff(c_267, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_264])).
% 2.45/1.44  tff(c_272, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_255, c_267])).
% 2.45/1.44  tff(c_275, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_38])).
% 2.45/1.44  tff(c_286, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_275])).
% 2.45/1.44  tff(c_287, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.44  tff(c_291, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_287])).
% 2.45/1.44  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.44  tff(c_304, plain, (![B_94, A_95]: (k10_relat_1(B_94, A_95)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_94), A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.44  tff(c_310, plain, (![B_96]: (k10_relat_1(B_96, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_4, c_304])).
% 2.45/1.44  tff(c_314, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_291, c_310])).
% 2.45/1.44  tff(c_341, plain, (![A_104, B_105, C_106, D_107]: (k8_relset_1(A_104, B_105, C_106, D_107)=k10_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.44  tff(c_344, plain, (![D_107]: (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', D_107)=k10_relat_1('#skF_3', D_107))), inference(resolution, [status(thm)], [c_286, c_341])).
% 2.45/1.44  tff(c_302, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_274, c_272, c_255, c_254, c_34])).
% 2.45/1.44  tff(c_345, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_344, c_302])).
% 2.45/1.44  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_345])).
% 2.45/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.44  
% 2.45/1.44  Inference rules
% 2.45/1.44  ----------------------
% 2.45/1.44  #Ref     : 0
% 2.45/1.44  #Sup     : 71
% 2.45/1.44  #Fact    : 0
% 2.45/1.44  #Define  : 0
% 2.45/1.44  #Split   : 3
% 2.45/1.44  #Chain   : 0
% 2.45/1.44  #Close   : 0
% 2.45/1.44  
% 2.45/1.44  Ordering : KBO
% 2.45/1.44  
% 2.45/1.44  Simplification rules
% 2.45/1.44  ----------------------
% 2.45/1.44  #Subsume      : 0
% 2.45/1.44  #Demod        : 43
% 2.45/1.44  #Tautology    : 44
% 2.45/1.44  #SimpNegUnit  : 3
% 2.45/1.44  #BackRed      : 13
% 2.45/1.44  
% 2.45/1.44  #Partial instantiations: 0
% 2.45/1.44  #Strategies tried      : 1
% 2.45/1.44  
% 2.45/1.44  Timing (in seconds)
% 2.45/1.44  ----------------------
% 2.45/1.44  Preprocessing        : 0.35
% 2.45/1.44  Parsing              : 0.19
% 2.45/1.44  CNF conversion       : 0.02
% 2.45/1.44  Main loop            : 0.22
% 2.45/1.44  Inferencing          : 0.08
% 2.45/1.44  Reduction            : 0.07
% 2.45/1.44  Demodulation         : 0.05
% 2.45/1.44  BG Simplification    : 0.01
% 2.45/1.44  Subsumption          : 0.03
% 2.45/1.44  Abstraction          : 0.01
% 2.45/1.44  MUC search           : 0.00
% 2.45/1.44  Cooper               : 0.00
% 2.45/1.44  Total                : 0.60
% 2.45/1.44  Index Insertion      : 0.00
% 2.45/1.44  Index Deletion       : 0.00
% 2.45/1.44  Index Matching       : 0.00
% 2.45/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
