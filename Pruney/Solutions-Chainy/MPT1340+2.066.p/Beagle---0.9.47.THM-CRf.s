%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:39 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  177 (39809 expanded)
%              Number of leaves         :   46 (13847 expanded)
%              Depth                    :   30
%              Number of atoms          :  487 (114348 expanded)
%              Number of equality atoms :  111 (24784 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
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

tff(f_157,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_153,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_72,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_80,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_72])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_79,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_72])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_105,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_60])).

tff(c_160,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_164,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_160])).

tff(c_58,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_106,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_58])).

tff(c_165,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_106])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_92,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_98,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_92])).

tff(c_102,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_98])).

tff(c_103,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_102])).

tff(c_174,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_103])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_111,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_105,c_111])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_120,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_124,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_105,c_120])).

tff(c_131,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_134,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_131])).

tff(c_137,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_134])).

tff(c_138,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_89,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_62])).

tff(c_175,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_89])).

tff(c_173,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_105])).

tff(c_234,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_237,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_173,c_234])).

tff(c_240,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_175,c_237])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_138,c_240])).

tff(c_243,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_258,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_105])).

tff(c_320,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_324,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_258,c_320])).

tff(c_256,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_106])).

tff(c_325,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_256])).

tff(c_259,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_89])).

tff(c_332,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_259])).

tff(c_331,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_258])).

tff(c_514,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( r2_funct_2(A_101,B_102,C_103,C_103)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(D_104,A_101,B_102)
      | ~ v1_funct_1(D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_518,plain,(
    ! [C_103] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_103,C_103)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_103,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_331,c_514])).

tff(c_566,plain,(
    ! [C_108] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_108,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_108,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_518])).

tff(c_571,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_566])).

tff(c_575,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_571])).

tff(c_330,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_324])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_422,plain,(
    ! [C_85,B_86,A_87] :
      ( v1_funct_2(k2_funct_1(C_85),B_86,A_87)
      | k2_relset_1(A_87,B_86,C_85) != B_86
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_425,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_422])).

tff(c_428,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_56,c_330,c_425])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_445,plain,(
    ! [C_92,B_93,A_94] :
      ( m1_subset_1(k2_funct_1(C_92),k1_zfmisc_1(k2_zfmisc_1(B_93,A_94)))
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_469,plain,(
    ! [C_92,B_93,A_94] :
      ( v1_relat_1(k2_funct_1(C_92))
      | ~ v1_relat_1(k2_zfmisc_1(B_93,A_94))
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_445,c_2])).

tff(c_480,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(k2_funct_1(C_95))
      | k2_relset_1(A_96,B_97,C_95) != B_97
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_469])).

tff(c_486,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_480])).

tff(c_490,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_56,c_330,c_486])).

tff(c_402,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_funct_1(k2_funct_1(C_79))
      | k2_relset_1(A_80,B_81,C_79) != B_81
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_79,A_80,B_81)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_405,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_402])).

tff(c_408,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_56,c_330,c_405])).

tff(c_28,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_491,plain,(
    ! [C_98,B_99,A_100] :
      ( v4_relat_1(k2_funct_1(C_98),B_99)
      | k2_relset_1(A_100,B_99,C_98) != B_99
      | ~ v2_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(C_98,A_100,B_99)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_445,c_28])).

tff(c_497,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_491])).

tff(c_501,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_56,c_330,c_497])).

tff(c_18,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_308,plain,(
    ! [A_70] :
      ( k1_relat_1(k2_funct_1(A_70)) = k2_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_24] :
      ( v1_partfun1(B_24,k1_relat_1(B_24))
      | ~ v4_relat_1(B_24,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_409,plain,(
    ! [A_82] :
      ( v1_partfun1(k2_funct_1(A_82),k1_relat_1(k2_funct_1(A_82)))
      | ~ v4_relat_1(k2_funct_1(A_82),k2_relat_1(A_82))
      | ~ v1_relat_1(k2_funct_1(A_82))
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_36])).

tff(c_412,plain,(
    ! [A_8] :
      ( v1_partfun1(k2_funct_1(A_8),k2_relat_1(A_8))
      | ~ v4_relat_1(k2_funct_1(A_8),k2_relat_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_409])).

tff(c_504,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_501,c_412])).

tff(c_510,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_490,c_504])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( k1_relat_1(B_24) = A_23
      | ~ v1_partfun1(B_24,A_23)
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_507,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_501,c_38])).

tff(c_513,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_507])).

tff(c_524,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_513])).

tff(c_24,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k1_relat_1(A_10)) != k5_relat_1(A_10,B_12)
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_527,plain,(
    ! [B_12] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_12
      | k5_relat_1(k2_funct_1('#skF_3'),B_12) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_12)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_24])).

tff(c_543,plain,(
    ! [B_12] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_12
      | k5_relat_1(k2_funct_1('#skF_3'),B_12) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_12)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_408,c_527])).

tff(c_576,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_543])).

tff(c_579,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_576])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_579])).

tff(c_586,plain,(
    ! [B_109] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_109
      | k5_relat_1(k2_funct_1('#skF_3'),B_109) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_109)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_590,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_586])).

tff(c_597,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_590])).

tff(c_612,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_615,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_612])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_615])).

tff(c_621,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_601,plain,(
    ! [B_110,A_111,C_112] :
      ( k2_relset_1(B_110,A_111,k2_funct_1(C_112)) = k2_relat_1(k2_funct_1(C_112))
      | k2_relset_1(A_111,B_110,C_112) != B_110
      | ~ v2_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ v1_funct_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_445,c_30])).

tff(c_607,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_601])).

tff(c_611,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_56,c_330,c_607])).

tff(c_686,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_611])).

tff(c_585,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_620,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_6,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_413,plain,(
    ! [A_83,B_84] :
      ( k2_funct_1(A_83) = B_84
      | k6_relat_1(k1_relat_1(A_83)) != k5_relat_1(A_83,B_84)
      | k2_relat_1(A_83) != k1_relat_1(B_84)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_808,plain,(
    ! [A_120] :
      ( k2_funct_1(k2_funct_1(A_120)) = A_120
      | k6_relat_1(k1_relat_1(k2_funct_1(A_120))) != k6_relat_1(k2_relat_1(A_120))
      | k2_relat_1(k2_funct_1(A_120)) != k1_relat_1(A_120)
      | ~ v2_funct_1(k2_funct_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120)
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_413])).

tff(c_824,plain,(
    ! [A_121] :
      ( k2_funct_1(k2_funct_1(A_121)) = A_121
      | k2_relat_1(k2_funct_1(A_121)) != k1_relat_1(A_121)
      | ~ v2_funct_1(k2_funct_1(A_121))
      | ~ v1_funct_1(k2_funct_1(A_121))
      | ~ v1_relat_1(k2_funct_1(A_121))
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_808])).

tff(c_840,plain,(
    ! [A_122] :
      ( k2_funct_1(k2_funct_1(A_122)) = A_122
      | k2_relat_1(k2_funct_1(A_122)) != k1_relat_1(A_122)
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_10,c_824])).

tff(c_856,plain,(
    ! [A_123] :
      ( k2_funct_1(k2_funct_1(A_123)) = A_123
      | k2_relat_1(k2_funct_1(A_123)) != k1_relat_1(A_123)
      | ~ v1_funct_1(k2_funct_1(A_123))
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_840])).

tff(c_872,plain,(
    ! [A_124] :
      ( k2_funct_1(k2_funct_1(A_124)) = A_124
      | k2_relat_1(k2_funct_1(A_124)) != k1_relat_1(A_124)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_6,c_856])).

tff(c_905,plain,(
    ! [A_127] :
      ( k2_funct_1(k2_funct_1(A_127)) = A_127
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_872])).

tff(c_42,plain,(
    ! [C_31,B_30,A_29] :
      ( m1_subset_1(k2_funct_1(C_31),k1_zfmisc_1(k2_zfmisc_1(B_30,A_29)))
      | k2_relset_1(A_29,B_30,C_31) != B_30
      | ~ v2_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1249,plain,(
    ! [A_139,B_140,A_141] :
      ( m1_subset_1(A_139,k1_zfmisc_1(k2_zfmisc_1(B_140,A_141)))
      | k2_relset_1(A_141,B_140,k2_funct_1(A_139)) != B_140
      | ~ v2_funct_1(k2_funct_1(A_139))
      | ~ m1_subset_1(k2_funct_1(A_139),k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(k2_funct_1(A_139),A_141,B_140)
      | ~ v1_funct_1(k2_funct_1(A_139))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_42])).

tff(c_1255,plain,(
    ! [B_140,A_141] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_140,A_141)))
      | k2_relset_1(A_141,B_140,k2_funct_1(k2_funct_1('#skF_3'))) != B_140
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_141,B_140)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_1249])).

tff(c_1273,plain,(
    ! [B_143,A_144] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_143,A_144)))
      | k2_relset_1(A_144,B_143,'#skF_3') != B_143
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2('#skF_3',A_144,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_408,c_585,c_64,c_620,c_620,c_56,c_620,c_620,c_1255])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_tops_2(A_34,B_35,C_36) = k2_funct_1(C_36)
      | ~ v2_funct_1(C_36)
      | k2_relset_1(A_34,B_35,C_36) != B_35
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1311,plain,(
    ! [B_143,A_144] :
      ( k2_tops_2(B_143,A_144,k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(B_143,A_144,k2_funct_1('#skF_3')) != A_144
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_143,A_144)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(A_144,B_143,'#skF_3') != B_143
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2('#skF_3',A_144,B_143) ) ),
    inference(resolution,[status(thm)],[c_1273,c_52])).

tff(c_1440,plain,(
    ! [B_158,A_159] :
      ( k2_tops_2(B_158,A_159,k2_funct_1('#skF_3')) = '#skF_3'
      | k2_relset_1(B_158,A_159,k2_funct_1('#skF_3')) != A_159
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_158,A_159)
      | k2_relset_1(A_159,B_158,'#skF_3') != B_158
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_159,B_158)))
      | ~ v1_funct_2('#skF_3',A_159,B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_585,c_620,c_1311])).

tff(c_1443,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_331,c_1440])).

tff(c_1446,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_330,c_428,c_686,c_1443])).

tff(c_429,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_tops_2(A_88,B_89,C_90) = k2_funct_1(C_90)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(A_88,B_89,C_90) != B_89
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_432,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_429])).

tff(c_435,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_332,c_330,c_56,c_432])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_118,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_80,c_79,c_79,c_79,c_54])).

tff(c_255,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_243,c_118])).

tff(c_401,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_325,c_325,c_255])).

tff(c_436,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_401])).

tff(c_1447,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_436])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_1447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.67  
% 4.03/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.67  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.03/1.67  
% 4.03/1.67  %Foreground sorts:
% 4.03/1.67  
% 4.03/1.67  
% 4.03/1.67  %Background operators:
% 4.03/1.67  
% 4.03/1.67  
% 4.03/1.67  %Foreground operators:
% 4.03/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.03/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.03/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.03/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.03/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.03/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.03/1.67  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.03/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.03/1.67  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.03/1.67  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.67  tff('#skF_1', type, '#skF_1': $i).
% 4.03/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.03/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.03/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.03/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.03/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.03/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.03/1.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.03/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.03/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.03/1.67  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.03/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.03/1.67  
% 4.29/1.70  tff(f_199, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 4.29/1.70  tff(f_157, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.29/1.70  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.29/1.70  tff(f_165, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.29/1.70  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.29/1.70  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.29/1.70  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.29/1.70  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.29/1.70  tff(f_115, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.29/1.70  tff(f_137, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.29/1.70  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.29/1.70  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.29/1.70  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.29/1.70  tff(f_54, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.29/1.70  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.29/1.70  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.29/1.70  tff(f_177, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.29/1.70  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_72, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.29/1.70  tff(c_80, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_72])).
% 4.29/1.70  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_79, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_72])).
% 4.29/1.70  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_105, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_60])).
% 4.29/1.70  tff(c_160, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.29/1.70  tff(c_164, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_160])).
% 4.29/1.70  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_106, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_58])).
% 4.29/1.70  tff(c_165, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_106])).
% 4.29/1.70  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_92, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.29/1.70  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_92])).
% 4.29/1.70  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_98])).
% 4.29/1.70  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_102])).
% 4.29/1.70  tff(c_174, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_103])).
% 4.29/1.70  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.29/1.70  tff(c_111, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.70  tff(c_114, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_105, c_111])).
% 4.29/1.70  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_114])).
% 4.29/1.70  tff(c_120, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.70  tff(c_124, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_120])).
% 4.29/1.70  tff(c_131, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.29/1.70  tff(c_134, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_131])).
% 4.29/1.70  tff(c_137, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_134])).
% 4.29/1.70  tff(c_138, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 4.29/1.70  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_89, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_62])).
% 4.29/1.70  tff(c_175, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_89])).
% 4.29/1.70  tff(c_173, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_105])).
% 4.29/1.70  tff(c_234, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.29/1.70  tff(c_237, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_173, c_234])).
% 4.29/1.70  tff(c_240, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_175, c_237])).
% 4.29/1.70  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_138, c_240])).
% 4.29/1.70  tff(c_243, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 4.29/1.70  tff(c_258, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_105])).
% 4.29/1.70  tff(c_320, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.29/1.70  tff(c_324, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_258, c_320])).
% 4.29/1.70  tff(c_256, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_106])).
% 4.29/1.70  tff(c_325, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_256])).
% 4.29/1.70  tff(c_259, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_89])).
% 4.29/1.70  tff(c_332, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_259])).
% 4.29/1.70  tff(c_331, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_258])).
% 4.29/1.70  tff(c_514, plain, (![A_101, B_102, C_103, D_104]: (r2_funct_2(A_101, B_102, C_103, C_103) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(D_104, A_101, B_102) | ~v1_funct_1(D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.70  tff(c_518, plain, (![C_103]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_103, C_103) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_103, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_103))), inference(resolution, [status(thm)], [c_331, c_514])).
% 4.29/1.70  tff(c_566, plain, (![C_108]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_108, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_108, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_108))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_518])).
% 4.29/1.70  tff(c_571, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_566])).
% 4.29/1.70  tff(c_575, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_571])).
% 4.29/1.70  tff(c_330, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_324])).
% 4.29/1.70  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_422, plain, (![C_85, B_86, A_87]: (v1_funct_2(k2_funct_1(C_85), B_86, A_87) | k2_relset_1(A_87, B_86, C_85)!=B_86 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.29/1.70  tff(c_425, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_422])).
% 4.29/1.70  tff(c_428, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_56, c_330, c_425])).
% 4.29/1.70  tff(c_16, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.29/1.70  tff(c_20, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.29/1.70  tff(c_10, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.29/1.70  tff(c_445, plain, (![C_92, B_93, A_94]: (m1_subset_1(k2_funct_1(C_92), k1_zfmisc_1(k2_zfmisc_1(B_93, A_94))) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.29/1.70  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.70  tff(c_469, plain, (![C_92, B_93, A_94]: (v1_relat_1(k2_funct_1(C_92)) | ~v1_relat_1(k2_zfmisc_1(B_93, A_94)) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_445, c_2])).
% 4.29/1.70  tff(c_480, plain, (![C_95, A_96, B_97]: (v1_relat_1(k2_funct_1(C_95)) | k2_relset_1(A_96, B_97, C_95)!=B_97 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_469])).
% 4.29/1.70  tff(c_486, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_480])).
% 4.29/1.70  tff(c_490, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_56, c_330, c_486])).
% 4.29/1.70  tff(c_402, plain, (![C_79, A_80, B_81]: (v1_funct_1(k2_funct_1(C_79)) | k2_relset_1(A_80, B_81, C_79)!=B_81 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_79, A_80, B_81) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.29/1.70  tff(c_405, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_402])).
% 4.29/1.70  tff(c_408, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_56, c_330, c_405])).
% 4.29/1.70  tff(c_28, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.70  tff(c_491, plain, (![C_98, B_99, A_100]: (v4_relat_1(k2_funct_1(C_98), B_99) | k2_relset_1(A_100, B_99, C_98)!=B_99 | ~v2_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(C_98, A_100, B_99) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_445, c_28])).
% 4.29/1.70  tff(c_497, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_491])).
% 4.29/1.70  tff(c_501, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_56, c_330, c_497])).
% 4.29/1.70  tff(c_18, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.29/1.70  tff(c_308, plain, (![A_70]: (k1_relat_1(k2_funct_1(A_70))=k2_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.29/1.70  tff(c_36, plain, (![B_24]: (v1_partfun1(B_24, k1_relat_1(B_24)) | ~v4_relat_1(B_24, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.29/1.70  tff(c_409, plain, (![A_82]: (v1_partfun1(k2_funct_1(A_82), k1_relat_1(k2_funct_1(A_82))) | ~v4_relat_1(k2_funct_1(A_82), k2_relat_1(A_82)) | ~v1_relat_1(k2_funct_1(A_82)) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_308, c_36])).
% 4.29/1.70  tff(c_412, plain, (![A_8]: (v1_partfun1(k2_funct_1(A_8), k2_relat_1(A_8)) | ~v4_relat_1(k2_funct_1(A_8), k2_relat_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_18, c_409])).
% 4.29/1.70  tff(c_504, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_501, c_412])).
% 4.29/1.70  tff(c_510, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_490, c_504])).
% 4.29/1.70  tff(c_38, plain, (![B_24, A_23]: (k1_relat_1(B_24)=A_23 | ~v1_partfun1(B_24, A_23) | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.29/1.70  tff(c_507, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_501, c_38])).
% 4.29/1.70  tff(c_513, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_507])).
% 4.29/1.70  tff(c_524, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_513])).
% 4.29/1.70  tff(c_24, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.29/1.70  tff(c_527, plain, (![B_12]: (k2_funct_1(k2_funct_1('#skF_3'))=B_12 | k5_relat_1(k2_funct_1('#skF_3'), B_12)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_12) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_524, c_24])).
% 4.29/1.70  tff(c_543, plain, (![B_12]: (k2_funct_1(k2_funct_1('#skF_3'))=B_12 | k5_relat_1(k2_funct_1('#skF_3'), B_12)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_12) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_408, c_527])).
% 4.29/1.70  tff(c_576, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_543])).
% 4.29/1.70  tff(c_579, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_576])).
% 4.29/1.70  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_579])).
% 4.29/1.70  tff(c_586, plain, (![B_109]: (k2_funct_1(k2_funct_1('#skF_3'))=B_109 | k5_relat_1(k2_funct_1('#skF_3'), B_109)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_109) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(splitRight, [status(thm)], [c_543])).
% 4.29/1.70  tff(c_590, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_586])).
% 4.29/1.70  tff(c_597, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_590])).
% 4.29/1.70  tff(c_612, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_597])).
% 4.29/1.70  tff(c_615, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_612])).
% 4.29/1.70  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_615])).
% 4.29/1.70  tff(c_621, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_597])).
% 4.29/1.70  tff(c_30, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.29/1.70  tff(c_601, plain, (![B_110, A_111, C_112]: (k2_relset_1(B_110, A_111, k2_funct_1(C_112))=k2_relat_1(k2_funct_1(C_112)) | k2_relset_1(A_111, B_110, C_112)!=B_110 | ~v2_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_2(C_112, A_111, B_110) | ~v1_funct_1(C_112))), inference(resolution, [status(thm)], [c_445, c_30])).
% 4.29/1.70  tff(c_607, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_601])).
% 4.29/1.70  tff(c_611, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_56, c_330, c_607])).
% 4.29/1.70  tff(c_686, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_611])).
% 4.29/1.70  tff(c_585, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_543])).
% 4.29/1.70  tff(c_620, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_597])).
% 4.29/1.70  tff(c_6, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.29/1.70  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.29/1.70  tff(c_413, plain, (![A_83, B_84]: (k2_funct_1(A_83)=B_84 | k6_relat_1(k1_relat_1(A_83))!=k5_relat_1(A_83, B_84) | k2_relat_1(A_83)!=k1_relat_1(B_84) | ~v2_funct_1(A_83) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.29/1.70  tff(c_808, plain, (![A_120]: (k2_funct_1(k2_funct_1(A_120))=A_120 | k6_relat_1(k1_relat_1(k2_funct_1(A_120)))!=k6_relat_1(k2_relat_1(A_120)) | k2_relat_1(k2_funct_1(A_120))!=k1_relat_1(A_120) | ~v2_funct_1(k2_funct_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_20, c_413])).
% 4.29/1.70  tff(c_824, plain, (![A_121]: (k2_funct_1(k2_funct_1(A_121))=A_121 | k2_relat_1(k2_funct_1(A_121))!=k1_relat_1(A_121) | ~v2_funct_1(k2_funct_1(A_121)) | ~v1_funct_1(k2_funct_1(A_121)) | ~v1_relat_1(k2_funct_1(A_121)) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_18, c_808])).
% 4.29/1.70  tff(c_840, plain, (![A_122]: (k2_funct_1(k2_funct_1(A_122))=A_122 | k2_relat_1(k2_funct_1(A_122))!=k1_relat_1(A_122) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_10, c_824])).
% 4.29/1.70  tff(c_856, plain, (![A_123]: (k2_funct_1(k2_funct_1(A_123))=A_123 | k2_relat_1(k2_funct_1(A_123))!=k1_relat_1(A_123) | ~v1_funct_1(k2_funct_1(A_123)) | ~v2_funct_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_8, c_840])).
% 4.29/1.70  tff(c_872, plain, (![A_124]: (k2_funct_1(k2_funct_1(A_124))=A_124 | k2_relat_1(k2_funct_1(A_124))!=k1_relat_1(A_124) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_6, c_856])).
% 4.29/1.70  tff(c_905, plain, (![A_127]: (k2_funct_1(k2_funct_1(A_127))=A_127 | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_16, c_872])).
% 4.29/1.70  tff(c_42, plain, (![C_31, B_30, A_29]: (m1_subset_1(k2_funct_1(C_31), k1_zfmisc_1(k2_zfmisc_1(B_30, A_29))) | k2_relset_1(A_29, B_30, C_31)!=B_30 | ~v2_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.29/1.70  tff(c_1249, plain, (![A_139, B_140, A_141]: (m1_subset_1(A_139, k1_zfmisc_1(k2_zfmisc_1(B_140, A_141))) | k2_relset_1(A_141, B_140, k2_funct_1(A_139))!=B_140 | ~v2_funct_1(k2_funct_1(A_139)) | ~m1_subset_1(k2_funct_1(A_139), k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(k2_funct_1(A_139), A_141, B_140) | ~v1_funct_1(k2_funct_1(A_139)) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_905, c_42])).
% 4.29/1.70  tff(c_1255, plain, (![B_140, A_141]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_140, A_141))) | k2_relset_1(A_141, B_140, k2_funct_1(k2_funct_1('#skF_3')))!=B_140 | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_141, B_140) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_620, c_1249])).
% 4.29/1.70  tff(c_1273, plain, (![B_143, A_144]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_143, A_144))) | k2_relset_1(A_144, B_143, '#skF_3')!=B_143 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2('#skF_3', A_144, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_408, c_585, c_64, c_620, c_620, c_56, c_620, c_620, c_1255])).
% 4.29/1.70  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_tops_2(A_34, B_35, C_36)=k2_funct_1(C_36) | ~v2_funct_1(C_36) | k2_relset_1(A_34, B_35, C_36)!=B_35 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.29/1.70  tff(c_1311, plain, (![B_143, A_144]: (k2_tops_2(B_143, A_144, k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(B_143, A_144, k2_funct_1('#skF_3'))!=A_144 | ~v1_funct_2(k2_funct_1('#skF_3'), B_143, A_144) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(A_144, B_143, '#skF_3')!=B_143 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2('#skF_3', A_144, B_143))), inference(resolution, [status(thm)], [c_1273, c_52])).
% 4.29/1.70  tff(c_1440, plain, (![B_158, A_159]: (k2_tops_2(B_158, A_159, k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(B_158, A_159, k2_funct_1('#skF_3'))!=A_159 | ~v1_funct_2(k2_funct_1('#skF_3'), B_158, A_159) | k2_relset_1(A_159, B_158, '#skF_3')!=B_158 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))) | ~v1_funct_2('#skF_3', A_159, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_585, c_620, c_1311])).
% 4.29/1.70  tff(c_1443, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_331, c_1440])).
% 4.29/1.70  tff(c_1446, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_330, c_428, c_686, c_1443])).
% 4.29/1.70  tff(c_429, plain, (![A_88, B_89, C_90]: (k2_tops_2(A_88, B_89, C_90)=k2_funct_1(C_90) | ~v2_funct_1(C_90) | k2_relset_1(A_88, B_89, C_90)!=B_89 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.29/1.70  tff(c_432, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_331, c_429])).
% 4.29/1.70  tff(c_435, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_332, c_330, c_56, c_432])).
% 4.29/1.70  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.29/1.70  tff(c_118, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_80, c_79, c_79, c_79, c_54])).
% 4.29/1.70  tff(c_255, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_243, c_118])).
% 4.29/1.70  tff(c_401, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_325, c_325, c_255])).
% 4.29/1.70  tff(c_436, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_401])).
% 4.29/1.70  tff(c_1447, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_436])).
% 4.29/1.70  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_1447])).
% 4.29/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.70  
% 4.29/1.70  Inference rules
% 4.29/1.70  ----------------------
% 4.29/1.70  #Ref     : 0
% 4.29/1.70  #Sup     : 298
% 4.29/1.70  #Fact    : 0
% 4.29/1.70  #Define  : 0
% 4.29/1.70  #Split   : 4
% 4.29/1.70  #Chain   : 0
% 4.29/1.70  #Close   : 0
% 4.29/1.70  
% 4.29/1.70  Ordering : KBO
% 4.29/1.70  
% 4.29/1.70  Simplification rules
% 4.29/1.70  ----------------------
% 4.29/1.70  #Subsume      : 27
% 4.29/1.70  #Demod        : 771
% 4.29/1.70  #Tautology    : 181
% 4.29/1.70  #SimpNegUnit  : 8
% 4.29/1.70  #BackRed      : 26
% 4.29/1.70  
% 4.29/1.70  #Partial instantiations: 0
% 4.29/1.70  #Strategies tried      : 1
% 4.29/1.70  
% 4.29/1.70  Timing (in seconds)
% 4.29/1.70  ----------------------
% 4.29/1.70  Preprocessing        : 0.36
% 4.29/1.70  Parsing              : 0.19
% 4.29/1.70  CNF conversion       : 0.02
% 4.29/1.70  Main loop            : 0.54
% 4.29/1.70  Inferencing          : 0.19
% 4.29/1.70  Reduction            : 0.20
% 4.29/1.70  Demodulation         : 0.15
% 4.29/1.70  BG Simplification    : 0.03
% 4.29/1.70  Subsumption          : 0.09
% 4.29/1.70  Abstraction          : 0.03
% 4.29/1.70  MUC search           : 0.00
% 4.29/1.70  Cooper               : 0.00
% 4.29/1.70  Total                : 0.97
% 4.29/1.70  Index Insertion      : 0.00
% 4.29/1.70  Index Deletion       : 0.00
% 4.29/1.70  Index Matching       : 0.00
% 4.29/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
