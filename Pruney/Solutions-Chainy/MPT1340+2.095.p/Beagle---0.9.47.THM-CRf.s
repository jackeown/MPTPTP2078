%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:44 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  153 (14429 expanded)
%              Number of leaves         :   46 (5160 expanded)
%              Depth                    :   24
%              Number of atoms          :  346 (43516 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_185,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_80,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_88,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_80])).

tff(c_74,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_87,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_80])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_68])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52,plain,(
    ! [A_29] :
      ( v1_funct_2(A_29,k1_relat_1(A_29),k2_relat_1(A_29))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    ! [A_29] :
      ( m1_subset_1(A_29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29))))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_328,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_539,plain,(
    ! [A_104] :
      ( k2_relat_1(A_104) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_104),k2_relat_1(A_104),A_104) = k1_relat_1(A_104)
      | ~ v1_funct_2(A_104,k1_relat_1(A_104),k2_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_50,c_328])).

tff(c_550,plain,(
    ! [A_105] :
      ( k2_relat_1(A_105) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_105),k2_relat_1(A_105),A_105) = k1_relat_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_52,c_539])).

tff(c_295,plain,(
    ! [A_70,B_71,C_72] :
      ( k8_relset_1(A_70,B_71,C_72,B_71) = k1_relset_1(A_70,B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_396,plain,(
    ! [A_94] :
      ( k8_relset_1(k1_relat_1(A_94),k2_relat_1(A_94),A_94,k2_relat_1(A_94)) = k1_relset_1(k1_relat_1(A_94),k2_relat_1(A_94),A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_50,c_295])).

tff(c_252,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k8_relset_1(A_60,B_61,C_62,D_63) = k10_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_257,plain,(
    ! [A_29,D_63] :
      ( k8_relset_1(k1_relat_1(A_29),k2_relat_1(A_29),A_29,D_63) = k10_relat_1(A_29,D_63)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_50,c_252])).

tff(c_402,plain,(
    ! [A_94] :
      ( k1_relset_1(k1_relat_1(A_94),k2_relat_1(A_94),A_94) = k10_relat_1(A_94,k2_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_257])).

tff(c_571,plain,(
    ! [A_106] :
      ( k10_relat_1(A_106,k2_relat_1(A_106)) = k1_relat_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106)
      | k2_relat_1(A_106) = k1_xboole_0
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_402])).

tff(c_175,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_175])).

tff(c_66,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_108,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_66])).

tff(c_180,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_108])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_70])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_93])).

tff(c_188,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_94])).

tff(c_187,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_101])).

tff(c_258,plain,(
    ! [D_63] : k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',D_63) = k10_relat_1('#skF_3',D_63) ),
    inference(resolution,[status(thm)],[c_187,c_252])).

tff(c_299,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_295])).

tff(c_302,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_299])).

tff(c_334,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_187,c_328])).

tff(c_338,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_302,c_334])).

tff(c_339,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_577,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_339])).

tff(c_589,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72,c_107,c_72,c_107,c_72,c_577])).

tff(c_593,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_58,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(k2_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_193,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_58])).

tff(c_197,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_193])).

tff(c_198,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_197])).

tff(c_617,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_198])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_617])).

tff(c_622,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_309,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_funct_2(A_77,B_78,D_79,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(D_79,A_77,B_78)
      | ~ v1_funct_1(D_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_313,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_309])).

tff(c_317,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_188,c_313])).

tff(c_629,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_317])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_634,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_188])).

tff(c_185,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_179])).

tff(c_632,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_185])).

tff(c_349,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_funct_1(k2_funct_1(C_86))
      | k2_relset_1(A_87,B_88,C_86) != B_88
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(C_86,A_87,B_88)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_355,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_349])).

tff(c_359,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_188,c_64,c_185,c_355])).

tff(c_385,plain,(
    ! [C_91,B_92,A_93] :
      ( v1_funct_2(k2_funct_1(C_91),B_92,A_93)
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_391,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_385])).

tff(c_395,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_188,c_64,c_185,c_391])).

tff(c_626,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_395])).

tff(c_14,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_633,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_187])).

tff(c_465,plain,(
    ! [C_100,B_101,A_102] :
      ( m1_subset_1(k2_funct_1(C_100),k1_zfmisc_1(k2_zfmisc_1(B_101,A_102)))
      | k2_relset_1(A_102,B_101,C_100) != B_101
      | ~ v2_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_970,plain,(
    ! [B_121,A_122,C_123] :
      ( k2_relset_1(B_121,A_122,k2_funct_1(C_123)) = k2_relat_1(k2_funct_1(C_123))
      | k2_relset_1(A_122,B_121,C_123) != B_121
      | ~ v2_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ v1_funct_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_465,c_20])).

tff(c_979,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_633,c_970])).

tff(c_990,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_634,c_64,c_632,c_979])).

tff(c_48,plain,(
    ! [C_28,A_26,B_27] :
      ( v1_funct_1(k2_funct_1(C_28))
      | k2_relset_1(A_26,B_27,C_28) != B_27
      | ~ v2_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2278,plain,(
    ! [C_194,B_195,A_196] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_194)))
      | k2_relset_1(B_195,A_196,k2_funct_1(C_194)) != A_196
      | ~ v2_funct_1(k2_funct_1(C_194))
      | ~ v1_funct_2(k2_funct_1(C_194),B_195,A_196)
      | ~ v1_funct_1(k2_funct_1(C_194))
      | k2_relset_1(A_196,B_195,C_194) != B_195
      | ~ v2_funct_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195)))
      | ~ v1_funct_2(C_194,A_196,B_195)
      | ~ v1_funct_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_465,c_48])).

tff(c_2290,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_633,c_2278])).

tff(c_2302,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_634,c_64,c_632,c_359,c_626,c_990,c_2290])).

tff(c_2644,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2302])).

tff(c_2647,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2644])).

tff(c_2651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72,c_64,c_2647])).

tff(c_2652,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2302])).

tff(c_3006,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2652])).

tff(c_3009,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3006])).

tff(c_3013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72,c_64,c_3009])).

tff(c_3015,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2652])).

tff(c_3025,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3015,c_990])).

tff(c_2653,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2302])).

tff(c_60,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_tops_2(A_32,B_33,C_34) = k2_funct_1(C_34)
      | ~ v2_funct_1(C_34)
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3379,plain,(
    ! [B_200,A_201,C_202] :
      ( k2_tops_2(B_200,A_201,k2_funct_1(C_202)) = k2_funct_1(k2_funct_1(C_202))
      | ~ v2_funct_1(k2_funct_1(C_202))
      | k2_relset_1(B_200,A_201,k2_funct_1(C_202)) != A_201
      | ~ v1_funct_2(k2_funct_1(C_202),B_200,A_201)
      | ~ v1_funct_1(k2_funct_1(C_202))
      | k2_relset_1(A_201,B_200,C_202) != B_200
      | ~ v2_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2(C_202,A_201,B_200)
      | ~ v1_funct_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_465,c_60])).

tff(c_3391,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_633,c_3379])).

tff(c_3403,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_634,c_64,c_632,c_359,c_626,c_3025,c_2653,c_3391])).

tff(c_449,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_tops_2(A_97,B_98,C_99) = k2_funct_1(C_99)
      | ~ v2_funct_1(C_99)
      | k2_relset_1(A_97,B_98,C_99) != B_98
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(C_99,A_97,B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_455,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_449])).

tff(c_459,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_188,c_185,c_64,c_455])).

tff(c_62,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_115,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_88,c_87,c_87,c_87,c_62])).

tff(c_186,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_180,c_180,c_115])).

tff(c_460,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_186])).

tff(c_624,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_622,c_460])).

tff(c_3528,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_624])).

tff(c_3535,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3528])).

tff(c_3538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72,c_64,c_629,c_3535])).

tff(c_3539,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_3550,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3539,c_198])).

tff(c_3554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.14  
% 6.01/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.14  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.01/2.14  
% 6.01/2.14  %Foreground sorts:
% 6.01/2.14  
% 6.01/2.14  
% 6.01/2.14  %Background operators:
% 6.01/2.14  
% 6.01/2.14  
% 6.01/2.14  %Foreground operators:
% 6.01/2.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.01/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.01/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.01/2.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.01/2.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.01/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.01/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.01/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.01/2.14  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.01/2.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.01/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.01/2.14  tff('#skF_2', type, '#skF_2': $i).
% 6.01/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.01/2.14  tff('#skF_1', type, '#skF_1': $i).
% 6.01/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.01/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.01/2.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.01/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.01/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.01/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.01/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.01/2.14  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.01/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.01/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.01/2.14  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.01/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.01/2.14  
% 6.01/2.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.01/2.17  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.01/2.17  tff(f_185, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 6.01/2.17  tff(f_143, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.01/2.17  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.01/2.17  tff(f_139, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.01/2.17  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.01/2.17  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 6.01/2.17  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.01/2.17  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.01/2.17  tff(f_151, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 6.01/2.17  tff(f_113, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.01/2.17  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.01/2.17  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.01/2.17  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.01/2.17  tff(f_47, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.01/2.17  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 6.01/2.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.01/2.17  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.01/2.17  tff(c_78, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_80, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.01/2.17  tff(c_88, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_80])).
% 6.01/2.17  tff(c_74, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_87, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_80])).
% 6.01/2.17  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_101, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_68])).
% 6.01/2.17  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.01/2.17  tff(c_104, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_101, c_4])).
% 6.01/2.17  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_104])).
% 6.01/2.17  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_52, plain, (![A_29]: (v1_funct_2(A_29, k1_relat_1(A_29), k2_relat_1(A_29)) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.01/2.17  tff(c_50, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29)))) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.01/2.17  tff(c_328, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.01/2.17  tff(c_539, plain, (![A_104]: (k2_relat_1(A_104)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_104), k2_relat_1(A_104), A_104)=k1_relat_1(A_104) | ~v1_funct_2(A_104, k1_relat_1(A_104), k2_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_50, c_328])).
% 6.01/2.17  tff(c_550, plain, (![A_105]: (k2_relat_1(A_105)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_105), k2_relat_1(A_105), A_105)=k1_relat_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_52, c_539])).
% 6.01/2.17  tff(c_295, plain, (![A_70, B_71, C_72]: (k8_relset_1(A_70, B_71, C_72, B_71)=k1_relset_1(A_70, B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.01/2.17  tff(c_396, plain, (![A_94]: (k8_relset_1(k1_relat_1(A_94), k2_relat_1(A_94), A_94, k2_relat_1(A_94))=k1_relset_1(k1_relat_1(A_94), k2_relat_1(A_94), A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_50, c_295])).
% 6.01/2.17  tff(c_252, plain, (![A_60, B_61, C_62, D_63]: (k8_relset_1(A_60, B_61, C_62, D_63)=k10_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.01/2.17  tff(c_257, plain, (![A_29, D_63]: (k8_relset_1(k1_relat_1(A_29), k2_relat_1(A_29), A_29, D_63)=k10_relat_1(A_29, D_63) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_50, c_252])).
% 6.01/2.17  tff(c_402, plain, (![A_94]: (k1_relset_1(k1_relat_1(A_94), k2_relat_1(A_94), A_94)=k10_relat_1(A_94, k2_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_396, c_257])).
% 6.01/2.17  tff(c_571, plain, (![A_106]: (k10_relat_1(A_106, k2_relat_1(A_106))=k1_relat_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106) | k2_relat_1(A_106)=k1_xboole_0 | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_550, c_402])).
% 6.01/2.17  tff(c_175, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.01/2.17  tff(c_179, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_175])).
% 6.01/2.17  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_108, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_66])).
% 6.01/2.17  tff(c_180, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_108])).
% 6.01/2.17  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_93, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_70])).
% 6.01/2.17  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_93])).
% 6.01/2.17  tff(c_188, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_94])).
% 6.01/2.17  tff(c_187, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_101])).
% 6.01/2.17  tff(c_258, plain, (![D_63]: (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', D_63)=k10_relat_1('#skF_3', D_63))), inference(resolution, [status(thm)], [c_187, c_252])).
% 6.01/2.17  tff(c_299, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_187, c_295])).
% 6.01/2.17  tff(c_302, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_299])).
% 6.01/2.17  tff(c_334, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_187, c_328])).
% 6.01/2.17  tff(c_338, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_302, c_334])).
% 6.01/2.17  tff(c_339, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_338])).
% 6.01/2.17  tff(c_577, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_571, c_339])).
% 6.01/2.17  tff(c_589, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_72, c_107, c_72, c_107, c_72, c_577])).
% 6.01/2.17  tff(c_593, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_589])).
% 6.01/2.17  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_58, plain, (![A_31]: (~v1_xboole_0(k2_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.01/2.17  tff(c_193, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_180, c_58])).
% 6.01/2.17  tff(c_197, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_193])).
% 6.01/2.17  tff(c_198, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_197])).
% 6.01/2.17  tff(c_617, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_593, c_198])).
% 6.01/2.17  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_617])).
% 6.01/2.17  tff(c_622, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_589])).
% 6.01/2.17  tff(c_309, plain, (![A_77, B_78, D_79]: (r2_funct_2(A_77, B_78, D_79, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(D_79, A_77, B_78) | ~v1_funct_1(D_79))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.01/2.17  tff(c_313, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_309])).
% 6.01/2.17  tff(c_317, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_188, c_313])).
% 6.01/2.17  tff(c_629, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_317])).
% 6.01/2.17  tff(c_18, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.01/2.17  tff(c_634, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_188])).
% 6.01/2.17  tff(c_185, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_179])).
% 6.01/2.17  tff(c_632, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_185])).
% 6.01/2.17  tff(c_349, plain, (![C_86, A_87, B_88]: (v1_funct_1(k2_funct_1(C_86)) | k2_relset_1(A_87, B_88, C_86)!=B_88 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(C_86, A_87, B_88) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.01/2.17  tff(c_355, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_349])).
% 6.01/2.17  tff(c_359, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_188, c_64, c_185, c_355])).
% 6.01/2.17  tff(c_385, plain, (![C_91, B_92, A_93]: (v1_funct_2(k2_funct_1(C_91), B_92, A_93) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.01/2.17  tff(c_391, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_385])).
% 6.01/2.17  tff(c_395, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_188, c_64, c_185, c_391])).
% 6.01/2.17  tff(c_626, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_395])).
% 6.01/2.17  tff(c_14, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.01/2.17  tff(c_8, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.01/2.17  tff(c_633, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_187])).
% 6.01/2.17  tff(c_465, plain, (![C_100, B_101, A_102]: (m1_subset_1(k2_funct_1(C_100), k1_zfmisc_1(k2_zfmisc_1(B_101, A_102))) | k2_relset_1(A_102, B_101, C_100)!=B_101 | ~v2_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.01/2.17  tff(c_20, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.01/2.17  tff(c_970, plain, (![B_121, A_122, C_123]: (k2_relset_1(B_121, A_122, k2_funct_1(C_123))=k2_relat_1(k2_funct_1(C_123)) | k2_relset_1(A_122, B_121, C_123)!=B_121 | ~v2_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2(C_123, A_122, B_121) | ~v1_funct_1(C_123))), inference(resolution, [status(thm)], [c_465, c_20])).
% 6.01/2.17  tff(c_979, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_633, c_970])).
% 6.01/2.17  tff(c_990, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_634, c_64, c_632, c_979])).
% 6.01/2.17  tff(c_48, plain, (![C_28, A_26, B_27]: (v1_funct_1(k2_funct_1(C_28)) | k2_relset_1(A_26, B_27, C_28)!=B_27 | ~v2_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.01/2.17  tff(c_2278, plain, (![C_194, B_195, A_196]: (v1_funct_1(k2_funct_1(k2_funct_1(C_194))) | k2_relset_1(B_195, A_196, k2_funct_1(C_194))!=A_196 | ~v2_funct_1(k2_funct_1(C_194)) | ~v1_funct_2(k2_funct_1(C_194), B_195, A_196) | ~v1_funct_1(k2_funct_1(C_194)) | k2_relset_1(A_196, B_195, C_194)!=B_195 | ~v2_funct_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))) | ~v1_funct_2(C_194, A_196, B_195) | ~v1_funct_1(C_194))), inference(resolution, [status(thm)], [c_465, c_48])).
% 6.01/2.17  tff(c_2290, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_633, c_2278])).
% 6.01/2.17  tff(c_2302, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_634, c_64, c_632, c_359, c_626, c_990, c_2290])).
% 6.01/2.17  tff(c_2644, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2302])).
% 6.01/2.17  tff(c_2647, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_2644])).
% 6.01/2.17  tff(c_2651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_72, c_64, c_2647])).
% 6.01/2.17  tff(c_2652, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2302])).
% 6.01/2.17  tff(c_3006, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2652])).
% 6.01/2.17  tff(c_3009, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_3006])).
% 6.01/2.17  tff(c_3013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_72, c_64, c_3009])).
% 6.01/2.17  tff(c_3015, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2652])).
% 6.01/2.17  tff(c_3025, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3015, c_990])).
% 6.01/2.17  tff(c_2653, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2302])).
% 6.01/2.17  tff(c_60, plain, (![A_32, B_33, C_34]: (k2_tops_2(A_32, B_33, C_34)=k2_funct_1(C_34) | ~v2_funct_1(C_34) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.17  tff(c_3379, plain, (![B_200, A_201, C_202]: (k2_tops_2(B_200, A_201, k2_funct_1(C_202))=k2_funct_1(k2_funct_1(C_202)) | ~v2_funct_1(k2_funct_1(C_202)) | k2_relset_1(B_200, A_201, k2_funct_1(C_202))!=A_201 | ~v1_funct_2(k2_funct_1(C_202), B_200, A_201) | ~v1_funct_1(k2_funct_1(C_202)) | k2_relset_1(A_201, B_200, C_202)!=B_200 | ~v2_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2(C_202, A_201, B_200) | ~v1_funct_1(C_202))), inference(resolution, [status(thm)], [c_465, c_60])).
% 6.01/2.17  tff(c_3391, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_633, c_3379])).
% 6.01/2.17  tff(c_3403, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_634, c_64, c_632, c_359, c_626, c_3025, c_2653, c_3391])).
% 6.01/2.17  tff(c_449, plain, (![A_97, B_98, C_99]: (k2_tops_2(A_97, B_98, C_99)=k2_funct_1(C_99) | ~v2_funct_1(C_99) | k2_relset_1(A_97, B_98, C_99)!=B_98 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(C_99, A_97, B_98) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.17  tff(c_455, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_449])).
% 6.01/2.17  tff(c_459, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_188, c_185, c_64, c_455])).
% 6.01/2.17  tff(c_62, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.01/2.17  tff(c_115, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_88, c_87, c_87, c_87, c_62])).
% 6.01/2.17  tff(c_186, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_180, c_180, c_115])).
% 6.01/2.17  tff(c_460, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_186])).
% 6.01/2.17  tff(c_624, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_622, c_460])).
% 6.01/2.17  tff(c_3528, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_624])).
% 6.01/2.17  tff(c_3535, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_3528])).
% 6.01/2.17  tff(c_3538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_72, c_64, c_629, c_3535])).
% 6.01/2.17  tff(c_3539, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_338])).
% 6.01/2.17  tff(c_3550, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3539, c_198])).
% 6.01/2.17  tff(c_3554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3550])).
% 6.01/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.17  
% 6.01/2.17  Inference rules
% 6.01/2.17  ----------------------
% 6.01/2.17  #Ref     : 0
% 6.01/2.17  #Sup     : 823
% 6.01/2.17  #Fact    : 0
% 6.01/2.17  #Define  : 0
% 6.01/2.17  #Split   : 7
% 6.01/2.17  #Chain   : 0
% 6.01/2.17  #Close   : 0
% 6.01/2.17  
% 6.01/2.17  Ordering : KBO
% 6.01/2.17  
% 6.01/2.17  Simplification rules
% 6.01/2.17  ----------------------
% 6.01/2.17  #Subsume      : 47
% 6.01/2.17  #Demod        : 1486
% 6.01/2.17  #Tautology    : 269
% 6.01/2.17  #SimpNegUnit  : 20
% 6.01/2.17  #BackRed      : 72
% 6.01/2.17  
% 6.01/2.17  #Partial instantiations: 0
% 6.01/2.17  #Strategies tried      : 1
% 6.01/2.17  
% 6.01/2.17  Timing (in seconds)
% 6.01/2.17  ----------------------
% 6.01/2.17  Preprocessing        : 0.36
% 6.01/2.17  Parsing              : 0.19
% 6.01/2.17  CNF conversion       : 0.02
% 6.01/2.17  Main loop            : 1.01
% 6.01/2.18  Inferencing          : 0.34
% 6.01/2.18  Reduction            : 0.36
% 6.01/2.18  Demodulation         : 0.27
% 6.01/2.18  BG Simplification    : 0.06
% 6.01/2.18  Subsumption          : 0.17
% 6.01/2.18  Abstraction          : 0.06
% 6.01/2.18  MUC search           : 0.00
% 6.01/2.18  Cooper               : 0.00
% 6.01/2.18  Total                : 1.43
% 6.01/2.18  Index Insertion      : 0.00
% 6.01/2.18  Index Deletion       : 0.00
% 6.01/2.18  Index Matching       : 0.00
% 6.01/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
