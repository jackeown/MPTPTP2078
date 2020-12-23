%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:48 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 232 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 668 expanded)
%              Number of equality atoms :   28 ( 197 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_36,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_47,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

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
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k9_relat_1(k2_funct_1(B_7),A_6) = k10_relat_1(B_7,A_6)
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_32])).

tff(c_26,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47,c_26])).

tff(c_147,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_tops_2(A_60,B_61,C_62) = k2_funct_1(C_62)
      | ~ v2_funct_1(C_62)
      | k2_relset_1(A_60,B_61,C_62) != B_61
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_153,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_147])).

tff(c_157,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58,c_72,c_24,c_153])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k2_tops_2(A_20,B_21,C_22),k1_zfmisc_1(k2_zfmisc_1(B_21,A_20)))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_164,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_16])).

tff(c_168,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58,c_65,c_164])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k7_relset_1(A_8,B_9,C_10,D_11) = k9_relat_1(C_10,D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_194,plain,(
    ! [D_11] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_11) = k9_relat_1(k2_funct_1('#skF_3'),D_11) ),
    inference(resolution,[status(thm)],[c_168,c_8])).

tff(c_86,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k8_relset_1(A_41,B_42,C_43,D_44) = k10_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [D_44] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_44) = k10_relat_1('#skF_3',D_44) ),
    inference(resolution,[status(thm)],[c_65,c_86])).

tff(c_22,plain,(
    k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_48,c_47,c_47,c_47,c_22])).

tff(c_91,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_90])).

tff(c_160,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_91])).

tff(c_216,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_160])).

tff(c_228,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_34,c_24,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.27/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.28  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.27/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.27/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.27/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.28  
% 2.27/1.30  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.30  tff(f_100, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k7_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tops_2)).
% 2.27/1.30  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.27/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.30  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.27/1.30  tff(f_66, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 2.27/1.30  tff(f_78, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 2.27/1.30  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.27/1.30  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.27/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.30  tff(c_38, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_40, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.27/1.30  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_40])).
% 2.27/1.30  tff(c_36, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_47, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_40])).
% 2.27/1.30  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_65, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_30])).
% 2.27/1.30  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.30  tff(c_68, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.27/1.30  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_68])).
% 2.27/1.30  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_6, plain, (![B_7, A_6]: (k9_relat_1(k2_funct_1(B_7), A_6)=k10_relat_1(B_7, A_6) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.30  tff(c_32, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_58, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_32])).
% 2.27/1.30  tff(c_26, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_72, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47, c_26])).
% 2.27/1.30  tff(c_147, plain, (![A_60, B_61, C_62]: (k2_tops_2(A_60, B_61, C_62)=k2_funct_1(C_62) | ~v2_funct_1(C_62) | k2_relset_1(A_60, B_61, C_62)!=B_61 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(C_62, A_60, B_61) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.27/1.30  tff(c_153, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_65, c_147])).
% 2.27/1.30  tff(c_157, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58, c_72, c_24, c_153])).
% 2.27/1.30  tff(c_16, plain, (![A_20, B_21, C_22]: (m1_subset_1(k2_tops_2(A_20, B_21, C_22), k1_zfmisc_1(k2_zfmisc_1(B_21, A_20))) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.30  tff(c_164, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_157, c_16])).
% 2.27/1.30  tff(c_168, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58, c_65, c_164])).
% 2.27/1.30  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k7_relset_1(A_8, B_9, C_10, D_11)=k9_relat_1(C_10, D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.30  tff(c_194, plain, (![D_11]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_11)=k9_relat_1(k2_funct_1('#skF_3'), D_11))), inference(resolution, [status(thm)], [c_168, c_8])).
% 2.27/1.30  tff(c_86, plain, (![A_41, B_42, C_43, D_44]: (k8_relset_1(A_41, B_42, C_43, D_44)=k10_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.30  tff(c_89, plain, (![D_44]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_44)=k10_relat_1('#skF_3', D_44))), inference(resolution, [status(thm)], [c_65, c_86])).
% 2.27/1.30  tff(c_22, plain, (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.30  tff(c_90, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_48, c_47, c_47, c_47, c_22])).
% 2.27/1.30  tff(c_91, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_90])).
% 2.27/1.30  tff(c_160, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_91])).
% 2.27/1.30  tff(c_216, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_160])).
% 2.27/1.30  tff(c_228, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_216])).
% 2.27/1.30  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_34, c_24, c_228])).
% 2.27/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  Inference rules
% 2.27/1.30  ----------------------
% 2.27/1.30  #Ref     : 0
% 2.27/1.30  #Sup     : 42
% 2.27/1.30  #Fact    : 0
% 2.27/1.30  #Define  : 0
% 2.27/1.30  #Split   : 1
% 2.27/1.30  #Chain   : 0
% 2.27/1.30  #Close   : 0
% 2.27/1.30  
% 2.27/1.30  Ordering : KBO
% 2.27/1.30  
% 2.27/1.30  Simplification rules
% 2.27/1.30  ----------------------
% 2.27/1.30  #Subsume      : 0
% 2.27/1.30  #Demod        : 47
% 2.27/1.30  #Tautology    : 17
% 2.27/1.30  #SimpNegUnit  : 0
% 2.27/1.30  #BackRed      : 6
% 2.27/1.30  
% 2.27/1.30  #Partial instantiations: 0
% 2.27/1.30  #Strategies tried      : 1
% 2.27/1.30  
% 2.27/1.30  Timing (in seconds)
% 2.27/1.30  ----------------------
% 2.27/1.30  Preprocessing        : 0.33
% 2.27/1.30  Parsing              : 0.17
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.21
% 2.50/1.30  Inferencing          : 0.08
% 2.50/1.30  Reduction            : 0.07
% 2.50/1.30  Demodulation         : 0.05
% 2.50/1.30  BG Simplification    : 0.01
% 2.50/1.30  Subsumption          : 0.03
% 2.50/1.30  Abstraction          : 0.01
% 2.50/1.30  MUC search           : 0.00
% 2.50/1.30  Cooper               : 0.00
% 2.50/1.30  Total                : 0.57
% 2.50/1.30  Index Insertion      : 0.00
% 2.50/1.30  Index Deletion       : 0.00
% 2.50/1.30  Index Matching       : 0.00
% 2.50/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
