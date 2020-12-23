%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:44 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   95 (1114 expanded)
%              Number of leaves         :   32 ( 417 expanded)
%              Depth                    :   14
%              Number of atoms          :  220 (3604 expanded)
%              Number of equality atoms :   45 ( 790 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
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

tff(f_74,axiom,(
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

tff(f_70,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_121,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_50])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_38])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_59,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_59])).

tff(c_124,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_funct_2(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_44,A_42,B_43)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_126,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_124])).

tff(c_129,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_126])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_36])).

tff(c_69,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64])).

tff(c_164,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_170,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_164])).

tff(c_174,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_69,c_34,c_170])).

tff(c_117,plain,(
    ! [A_39,B_40,C_41] :
      ( v1_funct_1(k2_tops_2(A_39,B_40,C_41))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_120,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_117])).

tff(c_123,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_120])).

tff(c_177,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_123])).

tff(c_130,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_2(k2_tops_2(A_45,B_46,C_47),B_46,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_132,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_135,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_132])).

tff(c_176,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_135])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k2_tops_2(A_16,B_17,C_18),k1_zfmisc_1(k2_zfmisc_1(B_17,A_16)))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_182,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_22])).

tff(c_186,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_76,c_182])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_tops_2(A_13,B_14,C_15) = k2_funct_1(C_15)
      | ~ v2_funct_1(C_15)
      | k2_relset_1(A_13,B_14,C_15) != B_14
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_197,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_186,c_20])).

tff(c_213,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_176,c_197])).

tff(c_235,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_388,plain,(
    ! [B_80,A_81,C_82] :
      ( k2_relset_1(u1_struct_0(B_80),u1_struct_0(A_81),k2_tops_2(u1_struct_0(A_81),u1_struct_0(B_80),C_82)) = k2_struct_0(A_81)
      | ~ v2_funct_1(C_82)
      | k2_relset_1(u1_struct_0(A_81),u1_struct_0(B_80),C_82) != k2_struct_0(B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0(B_80))))
      | ~ v1_funct_2(C_82,u1_struct_0(A_81),u1_struct_0(B_80))
      | ~ v1_funct_1(C_82)
      | ~ l1_struct_0(B_80)
      | v2_struct_0(B_80)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_409,plain,(
    ! [A_81,C_82] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_81),k2_tops_2(u1_struct_0(A_81),u1_struct_0('#skF_2'),C_82)) = k2_struct_0(A_81)
      | ~ v2_funct_1(C_82)
      | k2_relset_1(u1_struct_0(A_81),u1_struct_0('#skF_2'),C_82) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_82,u1_struct_0(A_81),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_82)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_388])).

tff(c_430,plain,(
    ! [A_81,C_82] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_81),k2_tops_2(u1_struct_0(A_81),k2_struct_0('#skF_2'),C_82)) = k2_struct_0(A_81)
      | ~ v2_funct_1(C_82)
      | k2_relset_1(u1_struct_0(A_81),k2_struct_0('#skF_2'),C_82) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_82,u1_struct_0(A_81),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_82)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_57,c_57,c_57,c_57,c_409])).

tff(c_443,plain,(
    ! [A_83,C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_83),k2_tops_2(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84)) = k2_struct_0(A_83)
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0(A_83),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_430])).

tff(c_452,plain,(
    ! [C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_443])).

tff(c_472,plain,(
    ! [C_85] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_85)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_85)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_85) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_85,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58,c_58,c_58,c_58,c_452])).

tff(c_481,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_472])).

tff(c_485,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_76,c_69,c_34,c_481])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_485])).

tff(c_488,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_494,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_497,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_494])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_42,c_34,c_497])).

tff(c_502,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_32,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_90,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_57,c_57,c_57,c_32])).

tff(c_178,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_90])).

tff(c_556,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_178])).

tff(c_614,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_556])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_42,c_34,c_129,c_614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.46  
% 3.20/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.46  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.46  
% 3.20/1.46  %Foreground sorts:
% 3.20/1.46  
% 3.20/1.46  
% 3.20/1.46  %Background operators:
% 3.20/1.46  
% 3.20/1.46  
% 3.20/1.46  %Foreground operators:
% 3.20/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.20/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.46  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.20/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.20/1.46  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.20/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.46  
% 3.20/1.48  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.20/1.48  tff(f_143, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.20/1.48  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.48  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.20/1.48  tff(f_70, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.20/1.48  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.20/1.48  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.20/1.48  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.20/1.48  tff(f_98, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.20/1.48  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.20/1.48  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.20/1.48  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_50, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.20/1.48  tff(c_58, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_50])).
% 3.20/1.48  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_50])).
% 3.20/1.48  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_38])).
% 3.20/1.48  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76, c_2])).
% 3.20/1.48  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 3.20/1.48  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_59, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40])).
% 3.20/1.48  tff(c_74, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_59])).
% 3.20/1.48  tff(c_124, plain, (![A_42, B_43, D_44]: (r2_funct_2(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_44, A_42, B_43) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.48  tff(c_126, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_124])).
% 3.20/1.48  tff(c_129, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_126])).
% 3.20/1.48  tff(c_12, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.48  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.48  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_36])).
% 3.20/1.48  tff(c_69, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_64])).
% 3.20/1.48  tff(c_164, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.48  tff(c_170, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_164])).
% 3.20/1.48  tff(c_174, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_69, c_34, c_170])).
% 3.20/1.48  tff(c_117, plain, (![A_39, B_40, C_41]: (v1_funct_1(k2_tops_2(A_39, B_40, C_41)) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_120, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_117])).
% 3.20/1.48  tff(c_123, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_120])).
% 3.20/1.48  tff(c_177, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_123])).
% 3.20/1.48  tff(c_130, plain, (![A_45, B_46, C_47]: (v1_funct_2(k2_tops_2(A_45, B_46, C_47), B_46, A_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_132, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_130])).
% 3.20/1.48  tff(c_135, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_132])).
% 3.20/1.48  tff(c_176, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_135])).
% 3.20/1.48  tff(c_22, plain, (![A_16, B_17, C_18]: (m1_subset_1(k2_tops_2(A_16, B_17, C_18), k1_zfmisc_1(k2_zfmisc_1(B_17, A_16))) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_182, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_174, c_22])).
% 3.20/1.48  tff(c_186, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_76, c_182])).
% 3.20/1.48  tff(c_20, plain, (![A_13, B_14, C_15]: (k2_tops_2(A_13, B_14, C_15)=k2_funct_1(C_15) | ~v2_funct_1(C_15) | k2_relset_1(A_13, B_14, C_15)!=B_14 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.48  tff(c_197, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_186, c_20])).
% 3.20/1.48  tff(c_213, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_176, c_197])).
% 3.20/1.48  tff(c_235, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_213])).
% 3.20/1.48  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_388, plain, (![B_80, A_81, C_82]: (k2_relset_1(u1_struct_0(B_80), u1_struct_0(A_81), k2_tops_2(u1_struct_0(A_81), u1_struct_0(B_80), C_82))=k2_struct_0(A_81) | ~v2_funct_1(C_82) | k2_relset_1(u1_struct_0(A_81), u1_struct_0(B_80), C_82)!=k2_struct_0(B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0(B_80)))) | ~v1_funct_2(C_82, u1_struct_0(A_81), u1_struct_0(B_80)) | ~v1_funct_1(C_82) | ~l1_struct_0(B_80) | v2_struct_0(B_80) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.20/1.48  tff(c_409, plain, (![A_81, C_82]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_81), k2_tops_2(u1_struct_0(A_81), u1_struct_0('#skF_2'), C_82))=k2_struct_0(A_81) | ~v2_funct_1(C_82) | k2_relset_1(u1_struct_0(A_81), u1_struct_0('#skF_2'), C_82)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_82, u1_struct_0(A_81), u1_struct_0('#skF_2')) | ~v1_funct_1(C_82) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_81))), inference(superposition, [status(thm), theory('equality')], [c_57, c_388])).
% 3.20/1.48  tff(c_430, plain, (![A_81, C_82]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_81), k2_tops_2(u1_struct_0(A_81), k2_struct_0('#skF_2'), C_82))=k2_struct_0(A_81) | ~v2_funct_1(C_82) | k2_relset_1(u1_struct_0(A_81), k2_struct_0('#skF_2'), C_82)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_82, u1_struct_0(A_81), k2_struct_0('#skF_2')) | ~v1_funct_1(C_82) | v2_struct_0('#skF_2') | ~l1_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_57, c_57, c_57, c_57, c_409])).
% 3.20/1.48  tff(c_443, plain, (![A_83, C_84]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_83), k2_tops_2(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84))=k2_struct_0(A_83) | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0(A_83), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0(A_83))), inference(negUnitSimplification, [status(thm)], [c_46, c_430])).
% 3.20/1.48  tff(c_452, plain, (![C_84]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84))=k2_struct_0('#skF_1') | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_443])).
% 3.20/1.48  tff(c_472, plain, (![C_85]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_85))=k2_struct_0('#skF_1') | ~v2_funct_1(C_85) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_85)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_85, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58, c_58, c_58, c_58, c_452])).
% 3.20/1.48  tff(c_481, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_174, c_472])).
% 3.20/1.48  tff(c_485, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_76, c_69, c_34, c_481])).
% 3.20/1.48  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_485])).
% 3.20/1.48  tff(c_488, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_213])).
% 3.20/1.48  tff(c_494, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_488])).
% 3.20/1.48  tff(c_497, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_494])).
% 3.20/1.48  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_42, c_34, c_497])).
% 3.20/1.48  tff(c_502, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_488])).
% 3.20/1.48  tff(c_32, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.20/1.48  tff(c_90, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_57, c_57, c_57, c_32])).
% 3.20/1.48  tff(c_178, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_90])).
% 3.20/1.48  tff(c_556, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_178])).
% 3.20/1.48  tff(c_614, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_556])).
% 3.20/1.48  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_42, c_34, c_129, c_614])).
% 3.20/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  Inference rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Ref     : 0
% 3.20/1.48  #Sup     : 118
% 3.20/1.48  #Fact    : 0
% 3.20/1.48  #Define  : 0
% 3.20/1.48  #Split   : 2
% 3.20/1.48  #Chain   : 0
% 3.20/1.48  #Close   : 0
% 3.20/1.48  
% 3.20/1.48  Ordering : KBO
% 3.20/1.48  
% 3.20/1.48  Simplification rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Subsume      : 3
% 3.20/1.48  #Demod        : 317
% 3.20/1.48  #Tautology    : 53
% 3.20/1.48  #SimpNegUnit  : 7
% 3.20/1.48  #BackRed      : 10
% 3.20/1.48  
% 3.20/1.48  #Partial instantiations: 0
% 3.20/1.48  #Strategies tried      : 1
% 3.20/1.48  
% 3.20/1.48  Timing (in seconds)
% 3.20/1.48  ----------------------
% 3.20/1.49  Preprocessing        : 0.35
% 3.20/1.49  Parsing              : 0.19
% 3.20/1.49  CNF conversion       : 0.02
% 3.20/1.49  Main loop            : 0.36
% 3.20/1.49  Inferencing          : 0.12
% 3.20/1.49  Reduction            : 0.14
% 3.20/1.49  Demodulation         : 0.10
% 3.20/1.49  BG Simplification    : 0.02
% 3.20/1.49  Subsumption          : 0.06
% 3.20/1.49  Abstraction          : 0.02
% 3.20/1.49  MUC search           : 0.00
% 3.20/1.49  Cooper               : 0.00
% 3.20/1.49  Total                : 0.75
% 3.20/1.49  Index Insertion      : 0.00
% 3.20/1.49  Index Deletion       : 0.00
% 3.20/1.49  Index Matching       : 0.00
% 3.20/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
