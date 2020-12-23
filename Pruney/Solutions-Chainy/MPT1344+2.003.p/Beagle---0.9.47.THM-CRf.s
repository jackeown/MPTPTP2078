%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:48 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 198 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 563 expanded)
%              Number of equality atoms :   33 ( 169 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                        & v2_funct_1(C) )
                     => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k7_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_61,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_37,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_37])).

tff(c_34,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_37])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_44,c_28])).

tff(c_63,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_63])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k9_relat_1(k2_funct_1(B_2),A_1) = k10_relat_1(B_2,A_1)
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30])).

tff(c_57,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_46])).

tff(c_24,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_44,c_24])).

tff(c_130,plain,(
    ! [C_57,B_58,A_59] :
      ( m1_subset_1(k2_funct_1(C_57),k1_zfmisc_1(k2_zfmisc_1(B_58,A_59)))
      | k2_relset_1(A_59,B_58,C_57) != B_58
      | ~ v2_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58)))
      | ~ v1_funct_2(C_57,A_59,B_58)
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k7_relset_1(A_6,B_7,C_8,D_9) = k9_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_68,A_69,C_70,D_71] :
      ( k7_relset_1(B_68,A_69,k2_funct_1(C_70),D_71) = k9_relat_1(k2_funct_1(C_70),D_71)
      | k2_relset_1(A_69,B_68,C_70) != B_68
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68)))
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ v1_funct_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_130,c_6])).

tff(c_186,plain,(
    ! [D_71] :
      ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_71) = k9_relat_1(k2_funct_1('#skF_3'),D_71)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_182])).

tff(c_190,plain,(
    ! [D_71] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_71) = k9_relat_1(k2_funct_1('#skF_3'),D_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57,c_22,c_58,c_186])).

tff(c_118,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_121,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_124,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57,c_58,c_22,c_121])).

tff(c_77,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k8_relset_1(A_38,B_39,C_40,D_41) = k10_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [D_41] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_41) = k10_relat_1('#skF_3',D_41) ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_20,plain,(
    k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_94,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_45,c_45,c_45,c_44,c_44,c_44,c_20])).

tff(c_125,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_94])).

tff(c_191,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_125])).

tff(c_214,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_32,c_22,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.65  
% 2.79/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.66  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.66  
% 2.79/1.66  %Foreground sorts:
% 2.79/1.66  
% 2.79/1.66  
% 2.79/1.66  %Background operators:
% 2.79/1.66  
% 2.79/1.66  
% 2.79/1.66  %Foreground operators:
% 2.79/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.79/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.79/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.66  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.79/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.66  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.79/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.79/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.79/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.66  
% 2.79/1.68  tff(f_99, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k7_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 2.79/1.68  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.79/1.68  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.68  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.79/1.68  tff(f_61, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 2.79/1.68  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.79/1.68  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 2.79/1.68  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.79/1.68  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_37, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.68  tff(c_45, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_37])).
% 2.79/1.68  tff(c_34, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_44, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_37])).
% 2.79/1.68  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_44, c_28])).
% 2.79/1.68  tff(c_63, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.68  tff(c_67, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_63])).
% 2.79/1.68  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_22, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_2, plain, (![B_2, A_1]: (k9_relat_1(k2_funct_1(B_2), A_1)=k10_relat_1(B_2, A_1) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.68  tff(c_30, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_30])).
% 2.79/1.68  tff(c_57, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_46])).
% 2.79/1.68  tff(c_24, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_58, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_44, c_24])).
% 2.79/1.68  tff(c_130, plain, (![C_57, B_58, A_59]: (m1_subset_1(k2_funct_1(C_57), k1_zfmisc_1(k2_zfmisc_1(B_58, A_59))) | k2_relset_1(A_59, B_58, C_57)!=B_58 | ~v2_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))) | ~v1_funct_2(C_57, A_59, B_58) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.79/1.68  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k7_relset_1(A_6, B_7, C_8, D_9)=k9_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.68  tff(c_182, plain, (![B_68, A_69, C_70, D_71]: (k7_relset_1(B_68, A_69, k2_funct_1(C_70), D_71)=k9_relat_1(k2_funct_1(C_70), D_71) | k2_relset_1(A_69, B_68, C_70)!=B_68 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))) | ~v1_funct_2(C_70, A_69, B_68) | ~v1_funct_1(C_70))), inference(resolution, [status(thm)], [c_130, c_6])).
% 2.79/1.68  tff(c_186, plain, (![D_71]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_71)=k9_relat_1(k2_funct_1('#skF_3'), D_71) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_182])).
% 2.79/1.68  tff(c_190, plain, (![D_71]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_71)=k9_relat_1(k2_funct_1('#skF_3'), D_71))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_57, c_22, c_58, c_186])).
% 2.79/1.68  tff(c_118, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.68  tff(c_121, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_118])).
% 2.79/1.68  tff(c_124, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_57, c_58, c_22, c_121])).
% 2.79/1.68  tff(c_77, plain, (![A_38, B_39, C_40, D_41]: (k8_relset_1(A_38, B_39, C_40, D_41)=k10_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.68  tff(c_80, plain, (![D_41]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_41)=k10_relat_1('#skF_3', D_41))), inference(resolution, [status(thm)], [c_56, c_77])).
% 2.79/1.68  tff(c_20, plain, (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.68  tff(c_94, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_45, c_45, c_45, c_44, c_44, c_44, c_20])).
% 2.79/1.68  tff(c_125, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_94])).
% 2.79/1.68  tff(c_191, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_125])).
% 2.79/1.68  tff(c_214, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 2.79/1.68  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_32, c_22, c_214])).
% 2.79/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.68  
% 2.79/1.68  Inference rules
% 2.79/1.68  ----------------------
% 2.79/1.68  #Ref     : 0
% 2.79/1.68  #Sup     : 41
% 2.79/1.68  #Fact    : 0
% 2.79/1.68  #Define  : 0
% 2.79/1.68  #Split   : 0
% 2.79/1.68  #Chain   : 0
% 2.79/1.68  #Close   : 0
% 2.79/1.68  
% 2.79/1.68  Ordering : KBO
% 2.79/1.68  
% 2.79/1.68  Simplification rules
% 2.79/1.68  ----------------------
% 2.79/1.68  #Subsume      : 0
% 2.79/1.68  #Demod        : 49
% 2.79/1.68  #Tautology    : 18
% 2.79/1.68  #SimpNegUnit  : 0
% 2.79/1.68  #BackRed      : 4
% 2.79/1.68  
% 2.79/1.68  #Partial instantiations: 0
% 2.79/1.68  #Strategies tried      : 1
% 2.79/1.68  
% 2.79/1.68  Timing (in seconds)
% 2.79/1.68  ----------------------
% 2.88/1.68  Preprocessing        : 0.48
% 2.88/1.68  Parsing              : 0.25
% 2.88/1.69  CNF conversion       : 0.03
% 2.88/1.69  Main loop            : 0.32
% 2.88/1.69  Inferencing          : 0.13
% 2.88/1.69  Reduction            : 0.10
% 2.88/1.69  Demodulation         : 0.08
% 2.88/1.69  BG Simplification    : 0.02
% 2.88/1.69  Subsumption          : 0.05
% 2.88/1.69  Abstraction          : 0.02
% 2.88/1.69  MUC search           : 0.00
% 2.88/1.69  Cooper               : 0.00
% 2.88/1.69  Total                : 0.85
% 2.88/1.69  Index Insertion      : 0.00
% 2.88/1.69  Index Deletion       : 0.00
% 2.88/1.69  Index Matching       : 0.00
% 2.88/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
