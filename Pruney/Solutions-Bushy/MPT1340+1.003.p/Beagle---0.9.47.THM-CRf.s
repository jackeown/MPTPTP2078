%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1340+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:50 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  111 (4679 expanded)
%              Number of leaves         :   33 (1692 expanded)
%              Depth                    :   19
%              Number of atoms          :  279 (14022 expanded)
%              Number of equality atoms :   60 (3541 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_97,axiom,(
    ! [A] :
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
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_43,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_32])).

tff(c_68,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_68])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_24,plain,(
    ! [A_32] :
      ( k2_funct_1(k2_funct_1(A_32)) = A_32
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_90,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_90])).

tff(c_30,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_63,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_30])).

tff(c_95,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_63])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52])).

tff(c_101,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_62])).

tff(c_102,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_61])).

tff(c_100,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_94])).

tff(c_156,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_156])).

tff(c_166,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_100,c_28,c_162])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k2_tops_2(A_8,B_9,C_10),k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_8])).

tff(c_177,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_102,c_173])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_177,c_14])).

tff(c_127,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_127])).

tff(c_133,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_130])).

tff(c_168,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_133])).

tff(c_134,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_2(k2_tops_2(A_48,B_49,C_50),B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_136,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_134])).

tff(c_139,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_136])).

tff(c_167,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_139])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_tops_2(A_5,B_6,C_7) = k2_funct_1(C_7)
      | ~ v2_funct_1(C_7)
      | k2_relset_1(A_5,B_6,C_7) != B_6
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_177,c_6])).

tff(c_195,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_167,c_181])).

tff(c_239,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_195])).

tff(c_240,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_103,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_50])).

tff(c_497,plain,(
    ! [B_95,A_96,C_97] :
      ( k2_relset_1(u1_struct_0(B_95),u1_struct_0(A_96),k2_tops_2(u1_struct_0(A_96),u1_struct_0(B_95),C_97)) = k2_struct_0(A_96)
      | ~ v2_funct_1(C_97)
      | k2_relset_1(u1_struct_0(A_96),u1_struct_0(B_95),C_97) != k2_struct_0(B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),u1_struct_0(B_95))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),u1_struct_0(B_95))
      | ~ v1_funct_1(C_97)
      | ~ l1_struct_0(B_95)
      | v2_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_515,plain,(
    ! [A_96,C_97] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_96),k2_tops_2(u1_struct_0(A_96),k2_relat_1('#skF_3'),C_97)) = k2_struct_0(A_96)
      | ~ v2_funct_1(C_97)
      | k2_relset_1(u1_struct_0(A_96),u1_struct_0('#skF_2'),C_97) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_97)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_497])).

tff(c_538,plain,(
    ! [A_96,C_97] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_96),k2_tops_2(u1_struct_0(A_96),k2_relat_1('#skF_3'),C_97)) = k2_struct_0(A_96)
      | ~ v2_funct_1(C_97)
      | k2_relset_1(u1_struct_0(A_96),k2_relat_1('#skF_3'),C_97) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_97)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103,c_103,c_103,c_95,c_103,c_515])).

tff(c_624,plain,(
    ! [A_110,C_111] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_110),k2_tops_2(u1_struct_0(A_110),k2_relat_1('#skF_3'),C_111)) = k2_struct_0(A_110)
      | ~ v2_funct_1(C_111)
      | k2_relset_1(u1_struct_0(A_110),k2_relat_1('#skF_3'),C_111) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_111,u1_struct_0(A_110),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_111)
      | ~ l1_struct_0(A_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_538])).

tff(c_639,plain,(
    ! [C_111] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_111)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_111)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_111) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_111,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_111)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_624])).

tff(c_662,plain,(
    ! [C_113] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_113)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_113)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_113) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_51,c_639])).

tff(c_671,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_662])).

tff(c_675,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_102,c_100,c_28,c_202,c_671])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_675])).

tff(c_678,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_689,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_690,plain,(
    ! [A_114,B_115,C_116] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_114),u1_struct_0(B_115),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(u1_struct_0(A_114),u1_struct_0(B_115),C_116) != k2_struct_0(B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114),u1_struct_0(B_115))))
      | ~ v1_funct_2(C_116,u1_struct_0(A_114),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ l1_struct_0(B_115)
      | ~ l1_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_703,plain,(
    ! [B_115,C_116] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_115),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_115),C_116) != k2_struct_0(B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_115))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_1'),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ l1_struct_0(B_115)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_690])).

tff(c_902,plain,(
    ! [B_140,C_141] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_140),C_141))
      | ~ v2_funct_1(C_141)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_140),C_141) != k2_struct_0(B_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_140))))
      | ~ v1_funct_2(C_141,k2_struct_0('#skF_1'),u1_struct_0(B_140))
      | ~ v1_funct_1(C_141)
      | ~ l1_struct_0(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_703])).

tff(c_909,plain,(
    ! [C_141] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_141))
      | ~ v2_funct_1(C_141)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_141) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_141,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_141)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_902])).

tff(c_918,plain,(
    ! [C_142] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_142))
      | ~ v2_funct_1(C_142)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_142) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_142,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103,c_95,c_103,c_103,c_909])).

tff(c_925,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_918])).

tff(c_929,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_100,c_28,c_166,c_925])).

tff(c_931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_689,c_929])).

tff(c_932,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_112,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_103,c_51,c_51,c_51,c_26])).

tff(c_169,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_112])).

tff(c_961,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_169])).

tff(c_980,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_961])).

tff(c_982,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36,c_28,c_980])).

tff(c_204,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( r2_funct_2(A_57,B_58,C_59,C_59)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(D_60,A_57,B_58)
      | ~ v1_funct_1(D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_210,plain,(
    ! [C_59] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_59,C_59)
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_59,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_102,c_204])).

tff(c_1159,plain,(
    ! [C_151] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_151,C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_151,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_210])).

tff(c_1166,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1159])).

tff(c_1173,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_1166])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1173])).

%------------------------------------------------------------------------------
