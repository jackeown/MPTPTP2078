%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:47 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 200 expanded)
%              Number of leaves         :   33 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 568 expanded)
%              Number of equality atoms :   34 ( 170 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                        & v2_funct_1(C) )
                     => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k8_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_70,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_66,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_36,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_65,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_30])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(k2_funct_1(B_7),A_6) = k9_relat_1(B_7,A_6)
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_32])).

tff(c_26,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_72,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_26])).

tff(c_140,plain,(
    ! [C_60,B_61,A_62] :
      ( m1_subset_1(k2_funct_1(C_60),k1_zfmisc_1(k2_zfmisc_1(B_61,A_62)))
      | k2_relset_1(A_62,B_61,C_60) != B_61
      | ~ v2_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61)))
      | ~ v1_funct_2(C_60,A_62,B_61)
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k8_relset_1(A_12,B_13,C_14,D_15) = k10_relat_1(C_14,D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_185,plain,(
    ! [B_70,A_71,C_72,D_73] :
      ( k8_relset_1(B_70,A_71,k2_funct_1(C_72),D_73) = k10_relat_1(k2_funct_1(C_72),D_73)
      | k2_relset_1(A_71,B_70,C_72) != B_70
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70)))
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ v1_funct_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_189,plain,(
    ! [D_73] :
      ( k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_73) = k10_relat_1(k2_funct_1('#skF_3'),D_73)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_65,c_185])).

tff(c_193,plain,(
    ! [D_73] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_73) = k10_relat_1(k2_funct_1('#skF_3'),D_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58,c_24,c_72,c_189])).

tff(c_128,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_tops_2(A_57,B_58,C_59) = k2_funct_1(C_59)
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_131,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_128])).

tff(c_134,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58,c_72,c_24,c_131])).

tff(c_100,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k7_relset_1(A_46,B_47,C_48,D_49) = k9_relat_1(C_48,D_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [D_49] : k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_49) = k9_relat_1('#skF_3',D_49) ),
    inference(resolution,[status(thm)],[c_65,c_100])).

tff(c_22,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_48,c_47,c_47,c_47,c_22])).

tff(c_104,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k9_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_90])).

tff(c_135,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),'#skF_4') != k9_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_104])).

tff(c_203,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),'#skF_4') != k9_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_135])).

tff(c_215,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_34,c_24,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.37/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.32  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.37/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.37/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.37/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.32  
% 2.37/1.34  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.34  tff(f_104, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 2.37/1.34  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.37/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.34  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.37/1.34  tff(f_66, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 2.37/1.34  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.37/1.34  tff(f_82, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 2.37/1.34  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.37/1.34  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.37/1.34  tff(c_38, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_40, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.34  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_40])).
% 2.37/1.34  tff(c_36, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_47, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_40])).
% 2.37/1.34  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_65, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_30])).
% 2.37/1.34  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.34  tff(c_68, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.37/1.34  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_68])).
% 2.37/1.34  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_6, plain, (![B_7, A_6]: (k10_relat_1(k2_funct_1(B_7), A_6)=k9_relat_1(B_7, A_6) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.34  tff(c_32, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_58, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_32])).
% 2.37/1.34  tff(c_26, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_72, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_26])).
% 2.37/1.34  tff(c_140, plain, (![C_60, B_61, A_62]: (m1_subset_1(k2_funct_1(C_60), k1_zfmisc_1(k2_zfmisc_1(B_61, A_62))) | k2_relset_1(A_62, B_61, C_60)!=B_61 | ~v2_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))) | ~v1_funct_2(C_60, A_62, B_61) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.34  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k8_relset_1(A_12, B_13, C_14, D_15)=k10_relat_1(C_14, D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.34  tff(c_185, plain, (![B_70, A_71, C_72, D_73]: (k8_relset_1(B_70, A_71, k2_funct_1(C_72), D_73)=k10_relat_1(k2_funct_1(C_72), D_73) | k2_relset_1(A_71, B_70, C_72)!=B_70 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))) | ~v1_funct_2(C_72, A_71, B_70) | ~v1_funct_1(C_72))), inference(resolution, [status(thm)], [c_140, c_10])).
% 2.37/1.34  tff(c_189, plain, (![D_73]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_73)=k10_relat_1(k2_funct_1('#skF_3'), D_73) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_65, c_185])).
% 2.37/1.34  tff(c_193, plain, (![D_73]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_73)=k10_relat_1(k2_funct_1('#skF_3'), D_73))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58, c_24, c_72, c_189])).
% 2.37/1.34  tff(c_128, plain, (![A_57, B_58, C_59]: (k2_tops_2(A_57, B_58, C_59)=k2_funct_1(C_59) | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.34  tff(c_131, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_65, c_128])).
% 2.37/1.34  tff(c_134, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58, c_72, c_24, c_131])).
% 2.37/1.34  tff(c_100, plain, (![A_46, B_47, C_48, D_49]: (k7_relset_1(A_46, B_47, C_48, D_49)=k9_relat_1(C_48, D_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_103, plain, (![D_49]: (k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_49)=k9_relat_1('#skF_3', D_49))), inference(resolution, [status(thm)], [c_65, c_100])).
% 2.37/1.34  tff(c_22, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.34  tff(c_90, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_48, c_47, c_47, c_47, c_22])).
% 2.37/1.34  tff(c_104, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k9_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_90])).
% 2.37/1.34  tff(c_135, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), '#skF_4')!=k9_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_104])).
% 2.37/1.34  tff(c_203, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_4')!=k9_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_135])).
% 2.37/1.34  tff(c_215, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_203])).
% 2.37/1.34  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_34, c_24, c_215])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 40
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 1
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Subsume      : 0
% 2.37/1.34  #Demod        : 45
% 2.37/1.34  #Tautology    : 18
% 2.37/1.34  #SimpNegUnit  : 0
% 2.37/1.34  #BackRed      : 4
% 2.37/1.34  
% 2.37/1.34  #Partial instantiations: 0
% 2.37/1.34  #Strategies tried      : 1
% 2.37/1.34  
% 2.37/1.34  Timing (in seconds)
% 2.37/1.34  ----------------------
% 2.37/1.34  Preprocessing        : 0.34
% 2.37/1.34  Parsing              : 0.19
% 2.37/1.34  CNF conversion       : 0.02
% 2.37/1.34  Main loop            : 0.22
% 2.37/1.34  Inferencing          : 0.08
% 2.37/1.34  Reduction            : 0.07
% 2.37/1.34  Demodulation         : 0.05
% 2.37/1.34  BG Simplification    : 0.02
% 2.37/1.34  Subsumption          : 0.03
% 2.37/1.34  Abstraction          : 0.02
% 2.37/1.34  MUC search           : 0.00
% 2.37/1.34  Cooper               : 0.00
% 2.37/1.34  Total                : 0.60
% 2.37/1.34  Index Insertion      : 0.00
% 2.37/1.34  Index Deletion       : 0.00
% 2.37/1.34  Index Matching       : 0.00
% 2.37/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
