%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:34 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  149 (14007 expanded)
%              Number of leaves         :   45 (5040 expanded)
%              Depth                    :   24
%              Number of atoms          :  339 (42734 expanded)
%              Number of equality atoms :   94 (10949 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_92,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_77,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_85,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_77])).

tff(c_72,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_84,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_77])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_84,c_66])).

tff(c_102,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_102])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_50,plain,(
    ! [A_27] :
      ( v1_funct_2(A_27,k1_relat_1(A_27),k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ! [A_27] :
      ( m1_subset_1(A_27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_27),k2_relat_1(A_27))))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_310,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_469,plain,(
    ! [A_98] :
      ( k2_relat_1(A_98) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_98),k2_relat_1(A_98),A_98) = k1_relat_1(A_98)
      | ~ v1_funct_2(A_98,k1_relat_1(A_98),k2_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_48,c_310])).

tff(c_539,plain,(
    ! [A_102] :
      ( k2_relat_1(A_102) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_102),k2_relat_1(A_102),A_102) = k1_relat_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_50,c_469])).

tff(c_243,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k8_relset_1(A_57,B_58,C_59,D_60) = k10_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    ! [A_27,D_60] :
      ( k8_relset_1(k1_relat_1(A_27),k2_relat_1(A_27),A_27,D_60) = k10_relat_1(A_27,D_60)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_48,c_243])).

tff(c_288,plain,(
    ! [A_71,B_72,C_73] :
      ( k8_relset_1(A_71,B_72,C_73,B_72) = k1_relset_1(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_347,plain,(
    ! [A_84] :
      ( k8_relset_1(k1_relat_1(A_84),k2_relat_1(A_84),A_84,k2_relat_1(A_84)) = k1_relset_1(k1_relat_1(A_84),k2_relat_1(A_84),A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_48,c_288])).

tff(c_360,plain,(
    ! [A_27] :
      ( k1_relset_1(k1_relat_1(A_27),k2_relat_1(A_27),A_27) = k10_relat_1(A_27,k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_347])).

tff(c_560,plain,(
    ! [A_103] :
      ( k10_relat_1(A_103,k2_relat_1(A_103)) = k1_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | k2_relat_1(A_103) = k1_xboole_0
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_360])).

tff(c_179,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_179])).

tff(c_64,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_96,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_84,c_64])).

tff(c_189,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_96])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_84,c_68])).

tff(c_197,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_94])).

tff(c_196,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_101])).

tff(c_248,plain,(
    ! [D_60] : k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',D_60) = k10_relat_1('#skF_3',D_60) ),
    inference(resolution,[status(thm)],[c_196,c_243])).

tff(c_290,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_288])).

tff(c_294,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_290])).

tff(c_313,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_196,c_310])).

tff(c_319,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_294,c_313])).

tff(c_321,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_566,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_321])).

tff(c_578,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_106,c_70,c_106,c_70,c_566])).

tff(c_582,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k2_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_202,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_56])).

tff(c_206,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_202])).

tff(c_207,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_206])).

tff(c_595,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_207])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_595])).

tff(c_600,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_331,plain,(
    ! [A_80,B_81,D_82] :
      ( r2_funct_2(A_80,B_81,D_82,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(D_82,A_80,B_81)
      | ~ v1_funct_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_333,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_331])).

tff(c_338,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_197,c_333])).

tff(c_616,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_338])).

tff(c_14,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_623,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_197])).

tff(c_194,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_187])).

tff(c_621,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_194])).

tff(c_372,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_funct_1(k2_funct_1(C_85))
      | k2_relset_1(A_86,B_87,C_85) != B_87
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_85,A_86,B_87)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_375,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_372])).

tff(c_381,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_197,c_62,c_194,c_375])).

tff(c_416,plain,(
    ! [C_90,B_91,A_92] :
      ( v1_funct_2(k2_funct_1(C_90),B_91,A_92)
      | k2_relset_1(A_92,B_91,C_90) != B_91
      | ~ v2_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91)))
      | ~ v1_funct_2(C_90,A_92,B_91)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_419,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_416])).

tff(c_425,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_197,c_62,c_194,c_419])).

tff(c_615,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_425])).

tff(c_10,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_622,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_196])).

tff(c_480,plain,(
    ! [C_99,B_100,A_101] :
      ( m1_subset_1(k2_funct_1(C_99),k1_zfmisc_1(k2_zfmisc_1(B_100,A_101)))
      | k2_relset_1(A_101,B_100,C_99) != B_100
      | ~ v2_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_relset_1(A_7,B_8,C_9) = k2_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1055,plain,(
    ! [B_122,A_123,C_124] :
      ( k2_relset_1(B_122,A_123,k2_funct_1(C_124)) = k2_relat_1(k2_funct_1(C_124))
      | k2_relset_1(A_123,B_122,C_124) != B_122
      | ~ v2_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_480,c_18])).

tff(c_1061,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_1055])).

tff(c_1074,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_623,c_62,c_621,c_1061])).

tff(c_46,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_funct_1(k2_funct_1(C_26))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3075,plain,(
    ! [C_190,B_191,A_192] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_190)))
      | k2_relset_1(B_191,A_192,k2_funct_1(C_190)) != A_192
      | ~ v2_funct_1(k2_funct_1(C_190))
      | ~ v1_funct_2(k2_funct_1(C_190),B_191,A_192)
      | ~ v1_funct_1(k2_funct_1(C_190))
      | k2_relset_1(A_192,B_191,C_190) != B_191
      | ~ v2_funct_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_2(C_190,A_192,B_191)
      | ~ v1_funct_1(C_190) ) ),
    inference(resolution,[status(thm)],[c_480,c_46])).

tff(c_3087,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_3075])).

tff(c_3104,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_623,c_62,c_621,c_381,c_615,c_1074,c_3087])).

tff(c_3247,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3104])).

tff(c_3250,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_3247])).

tff(c_3254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_62,c_3250])).

tff(c_3255,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3104])).

tff(c_3257,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3255])).

tff(c_3260,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3257])).

tff(c_3264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_62,c_3260])).

tff(c_3266,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3255])).

tff(c_3285,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3266,c_1074])).

tff(c_3256,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3104])).

tff(c_58,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_tops_2(A_30,B_31,C_32) = k2_funct_1(C_32)
      | ~ v2_funct_1(C_32)
      | k2_relset_1(A_30,B_31,C_32) != B_31
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3654,plain,(
    ! [B_196,A_197,C_198] :
      ( k2_tops_2(B_196,A_197,k2_funct_1(C_198)) = k2_funct_1(k2_funct_1(C_198))
      | ~ v2_funct_1(k2_funct_1(C_198))
      | k2_relset_1(B_196,A_197,k2_funct_1(C_198)) != A_197
      | ~ v1_funct_2(k2_funct_1(C_198),B_196,A_197)
      | ~ v1_funct_1(k2_funct_1(C_198))
      | k2_relset_1(A_197,B_196,C_198) != B_196
      | ~ v2_funct_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196)))
      | ~ v1_funct_2(C_198,A_197,B_196)
      | ~ v1_funct_1(C_198) ) ),
    inference(resolution,[status(thm)],[c_480,c_58])).

tff(c_3666,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_3654])).

tff(c_3683,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_623,c_62,c_621,c_381,c_615,c_3285,c_3256,c_3666])).

tff(c_453,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_tops_2(A_95,B_96,C_97) = k2_funct_1(C_97)
      | ~ v2_funct_1(C_97)
      | k2_relset_1(A_95,B_96,C_97) != B_96
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_456,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_453])).

tff(c_462,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_197,c_194,c_62,c_456])).

tff(c_60,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_111,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_85,c_84,c_84,c_84,c_60])).

tff(c_195,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_189,c_111])).

tff(c_464,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_195])).

tff(c_613,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_600,c_464])).

tff(c_3687,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3683,c_613])).

tff(c_3694,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3687])).

tff(c_3697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_62,c_616,c_3694])).

tff(c_3698,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_3708,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_207])).

tff(c_3712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.24  
% 6.21/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.24  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.21/2.24  
% 6.21/2.24  %Foreground sorts:
% 6.21/2.24  
% 6.21/2.24  
% 6.21/2.24  %Background operators:
% 6.21/2.24  
% 6.21/2.24  
% 6.21/2.24  %Foreground operators:
% 6.21/2.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.21/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.21/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.21/2.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.21/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.21/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.21/2.24  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.21/2.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.21/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.21/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.24  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.21/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.21/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.21/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.21/2.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.21/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.24  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.21/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.24  
% 6.45/2.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.45/2.27  tff(f_180, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 6.45/2.27  tff(f_138, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.45/2.27  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.45/2.27  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.45/2.27  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.45/2.27  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.45/2.27  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 6.45/2.27  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.45/2.27  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 6.45/2.27  tff(f_108, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.45/2.27  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.45/2.27  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.45/2.27  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.45/2.27  tff(f_38, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.45/2.27  tff(f_158, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.45/2.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.45/2.27  tff(c_76, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_77, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.27  tff(c_85, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_77])).
% 6.45/2.27  tff(c_72, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_84, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_77])).
% 6.45/2.27  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_101, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_84, c_66])).
% 6.45/2.27  tff(c_102, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.45/2.27  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_102])).
% 6.45/2.27  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_50, plain, (![A_27]: (v1_funct_2(A_27, k1_relat_1(A_27), k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.45/2.27  tff(c_48, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_27), k2_relat_1(A_27)))) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.45/2.27  tff(c_310, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.45/2.27  tff(c_469, plain, (![A_98]: (k2_relat_1(A_98)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_98), k2_relat_1(A_98), A_98)=k1_relat_1(A_98) | ~v1_funct_2(A_98, k1_relat_1(A_98), k2_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_48, c_310])).
% 6.45/2.27  tff(c_539, plain, (![A_102]: (k2_relat_1(A_102)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_102), k2_relat_1(A_102), A_102)=k1_relat_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_50, c_469])).
% 6.45/2.27  tff(c_243, plain, (![A_57, B_58, C_59, D_60]: (k8_relset_1(A_57, B_58, C_59, D_60)=k10_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.45/2.27  tff(c_249, plain, (![A_27, D_60]: (k8_relset_1(k1_relat_1(A_27), k2_relat_1(A_27), A_27, D_60)=k10_relat_1(A_27, D_60) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_48, c_243])).
% 6.45/2.27  tff(c_288, plain, (![A_71, B_72, C_73]: (k8_relset_1(A_71, B_72, C_73, B_72)=k1_relset_1(A_71, B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.45/2.27  tff(c_347, plain, (![A_84]: (k8_relset_1(k1_relat_1(A_84), k2_relat_1(A_84), A_84, k2_relat_1(A_84))=k1_relset_1(k1_relat_1(A_84), k2_relat_1(A_84), A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_48, c_288])).
% 6.45/2.27  tff(c_360, plain, (![A_27]: (k1_relset_1(k1_relat_1(A_27), k2_relat_1(A_27), A_27)=k10_relat_1(A_27, k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_249, c_347])).
% 6.45/2.27  tff(c_560, plain, (![A_103]: (k10_relat_1(A_103, k2_relat_1(A_103))=k1_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | k2_relat_1(A_103)=k1_xboole_0 | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_539, c_360])).
% 6.45/2.27  tff(c_179, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.45/2.27  tff(c_187, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_179])).
% 6.45/2.27  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_96, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_84, c_64])).
% 6.45/2.27  tff(c_189, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_96])).
% 6.45/2.27  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_84, c_68])).
% 6.45/2.27  tff(c_197, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_94])).
% 6.45/2.27  tff(c_196, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_101])).
% 6.45/2.27  tff(c_248, plain, (![D_60]: (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', D_60)=k10_relat_1('#skF_3', D_60))), inference(resolution, [status(thm)], [c_196, c_243])).
% 6.45/2.27  tff(c_290, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_196, c_288])).
% 6.45/2.27  tff(c_294, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_290])).
% 6.45/2.27  tff(c_313, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_196, c_310])).
% 6.45/2.27  tff(c_319, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_294, c_313])).
% 6.45/2.27  tff(c_321, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_319])).
% 6.45/2.27  tff(c_566, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_560, c_321])).
% 6.45/2.27  tff(c_578, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_106, c_70, c_106, c_70, c_566])).
% 6.45/2.27  tff(c_582, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_578])).
% 6.45/2.27  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_56, plain, (![A_29]: (~v1_xboole_0(k2_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.45/2.27  tff(c_202, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_189, c_56])).
% 6.45/2.27  tff(c_206, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_202])).
% 6.45/2.27  tff(c_207, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_206])).
% 6.45/2.27  tff(c_595, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_582, c_207])).
% 6.45/2.27  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_595])).
% 6.45/2.27  tff(c_600, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_578])).
% 6.45/2.27  tff(c_331, plain, (![A_80, B_81, D_82]: (r2_funct_2(A_80, B_81, D_82, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(D_82, A_80, B_81) | ~v1_funct_1(D_82))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.45/2.27  tff(c_333, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_196, c_331])).
% 6.45/2.27  tff(c_338, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_197, c_333])).
% 6.45/2.27  tff(c_616, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_338])).
% 6.45/2.27  tff(c_14, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.45/2.27  tff(c_623, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_197])).
% 6.45/2.27  tff(c_194, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_187])).
% 6.45/2.27  tff(c_621, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_194])).
% 6.45/2.27  tff(c_372, plain, (![C_85, A_86, B_87]: (v1_funct_1(k2_funct_1(C_85)) | k2_relset_1(A_86, B_87, C_85)!=B_87 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_85, A_86, B_87) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.45/2.27  tff(c_375, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_196, c_372])).
% 6.45/2.27  tff(c_381, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_197, c_62, c_194, c_375])).
% 6.45/2.27  tff(c_416, plain, (![C_90, B_91, A_92]: (v1_funct_2(k2_funct_1(C_90), B_91, A_92) | k2_relset_1(A_92, B_91, C_90)!=B_91 | ~v2_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))) | ~v1_funct_2(C_90, A_92, B_91) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.45/2.27  tff(c_419, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_196, c_416])).
% 6.45/2.27  tff(c_425, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_197, c_62, c_194, c_419])).
% 6.45/2.27  tff(c_615, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_425])).
% 6.45/2.27  tff(c_10, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.45/2.27  tff(c_4, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.45/2.27  tff(c_622, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_196])).
% 6.45/2.27  tff(c_480, plain, (![C_99, B_100, A_101]: (m1_subset_1(k2_funct_1(C_99), k1_zfmisc_1(k2_zfmisc_1(B_100, A_101))) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.45/2.27  tff(c_18, plain, (![A_7, B_8, C_9]: (k2_relset_1(A_7, B_8, C_9)=k2_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.45/2.27  tff(c_1055, plain, (![B_122, A_123, C_124]: (k2_relset_1(B_122, A_123, k2_funct_1(C_124))=k2_relat_1(k2_funct_1(C_124)) | k2_relset_1(A_123, B_122, C_124)!=B_122 | ~v2_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~v1_funct_2(C_124, A_123, B_122) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_480, c_18])).
% 6.45/2.27  tff(c_1061, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_622, c_1055])).
% 6.45/2.27  tff(c_1074, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_623, c_62, c_621, c_1061])).
% 6.45/2.27  tff(c_46, plain, (![C_26, A_24, B_25]: (v1_funct_1(k2_funct_1(C_26)) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.45/2.27  tff(c_3075, plain, (![C_190, B_191, A_192]: (v1_funct_1(k2_funct_1(k2_funct_1(C_190))) | k2_relset_1(B_191, A_192, k2_funct_1(C_190))!=A_192 | ~v2_funct_1(k2_funct_1(C_190)) | ~v1_funct_2(k2_funct_1(C_190), B_191, A_192) | ~v1_funct_1(k2_funct_1(C_190)) | k2_relset_1(A_192, B_191, C_190)!=B_191 | ~v2_funct_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_2(C_190, A_192, B_191) | ~v1_funct_1(C_190))), inference(resolution, [status(thm)], [c_480, c_46])).
% 6.45/2.27  tff(c_3087, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_622, c_3075])).
% 6.45/2.27  tff(c_3104, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_623, c_62, c_621, c_381, c_615, c_1074, c_3087])).
% 6.45/2.27  tff(c_3247, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3104])).
% 6.45/2.27  tff(c_3250, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_3247])).
% 6.45/2.27  tff(c_3254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_62, c_3250])).
% 6.45/2.27  tff(c_3255, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3104])).
% 6.45/2.27  tff(c_3257, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_3255])).
% 6.45/2.27  tff(c_3260, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_3257])).
% 6.45/2.27  tff(c_3264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_62, c_3260])).
% 6.45/2.27  tff(c_3266, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3255])).
% 6.45/2.27  tff(c_3285, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3266, c_1074])).
% 6.45/2.27  tff(c_3256, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3104])).
% 6.45/2.27  tff(c_58, plain, (![A_30, B_31, C_32]: (k2_tops_2(A_30, B_31, C_32)=k2_funct_1(C_32) | ~v2_funct_1(C_32) | k2_relset_1(A_30, B_31, C_32)!=B_31 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.45/2.27  tff(c_3654, plain, (![B_196, A_197, C_198]: (k2_tops_2(B_196, A_197, k2_funct_1(C_198))=k2_funct_1(k2_funct_1(C_198)) | ~v2_funct_1(k2_funct_1(C_198)) | k2_relset_1(B_196, A_197, k2_funct_1(C_198))!=A_197 | ~v1_funct_2(k2_funct_1(C_198), B_196, A_197) | ~v1_funct_1(k2_funct_1(C_198)) | k2_relset_1(A_197, B_196, C_198)!=B_196 | ~v2_funct_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))) | ~v1_funct_2(C_198, A_197, B_196) | ~v1_funct_1(C_198))), inference(resolution, [status(thm)], [c_480, c_58])).
% 6.45/2.27  tff(c_3666, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_622, c_3654])).
% 6.45/2.27  tff(c_3683, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_623, c_62, c_621, c_381, c_615, c_3285, c_3256, c_3666])).
% 6.45/2.27  tff(c_453, plain, (![A_95, B_96, C_97]: (k2_tops_2(A_95, B_96, C_97)=k2_funct_1(C_97) | ~v2_funct_1(C_97) | k2_relset_1(A_95, B_96, C_97)!=B_96 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.45/2.27  tff(c_456, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_196, c_453])).
% 6.45/2.27  tff(c_462, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_197, c_194, c_62, c_456])).
% 6.45/2.27  tff(c_60, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.45/2.27  tff(c_111, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_85, c_84, c_84, c_84, c_60])).
% 6.45/2.27  tff(c_195, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_189, c_111])).
% 6.45/2.27  tff(c_464, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_195])).
% 6.45/2.27  tff(c_613, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_600, c_464])).
% 6.45/2.27  tff(c_3687, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3683, c_613])).
% 6.45/2.27  tff(c_3694, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_3687])).
% 6.45/2.27  tff(c_3697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_62, c_616, c_3694])).
% 6.45/2.27  tff(c_3698, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_319])).
% 6.45/2.27  tff(c_3708, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_207])).
% 6.45/2.27  tff(c_3712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3708])).
% 6.45/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.27  
% 6.45/2.27  Inference rules
% 6.45/2.27  ----------------------
% 6.45/2.27  #Ref     : 0
% 6.45/2.27  #Sup     : 857
% 6.45/2.27  #Fact    : 0
% 6.45/2.27  #Define  : 0
% 6.45/2.27  #Split   : 7
% 6.45/2.27  #Chain   : 0
% 6.45/2.27  #Close   : 0
% 6.45/2.27  
% 6.45/2.27  Ordering : KBO
% 6.45/2.27  
% 6.45/2.27  Simplification rules
% 6.45/2.27  ----------------------
% 6.45/2.27  #Subsume      : 47
% 6.45/2.27  #Demod        : 1531
% 6.45/2.27  #Tautology    : 295
% 6.45/2.27  #SimpNegUnit  : 26
% 6.45/2.27  #BackRed      : 72
% 6.45/2.27  
% 6.45/2.27  #Partial instantiations: 0
% 6.45/2.27  #Strategies tried      : 1
% 6.45/2.27  
% 6.45/2.27  Timing (in seconds)
% 6.45/2.27  ----------------------
% 6.45/2.27  Preprocessing        : 0.38
% 6.45/2.27  Parsing              : 0.20
% 6.45/2.27  CNF conversion       : 0.02
% 6.45/2.27  Main loop            : 1.09
% 6.45/2.27  Inferencing          : 0.36
% 6.45/2.27  Reduction            : 0.40
% 6.45/2.27  Demodulation         : 0.31
% 6.45/2.27  BG Simplification    : 0.06
% 6.45/2.27  Subsumption          : 0.19
% 6.45/2.27  Abstraction          : 0.06
% 6.45/2.27  MUC search           : 0.00
% 6.45/2.27  Cooper               : 0.00
% 6.45/2.27  Total                : 1.53
% 6.45/2.27  Index Insertion      : 0.00
% 6.45/2.27  Index Deletion       : 0.00
% 6.45/2.27  Index Matching       : 0.00
% 6.45/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
