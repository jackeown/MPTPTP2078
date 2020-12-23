%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   95 (1193 expanded)
%              Number of leaves         :   31 ( 460 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (3973 expanded)
%              Number of equality atoms :   51 ( 877 expanded)
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

tff(f_144,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_104,axiom,(
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

tff(f_122,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_43,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_32])).

tff(c_67,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_34])).

tff(c_89,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_funct_2(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_41,A_39,B_40)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_89])).

tff(c_94,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_funct_1(k2_funct_1(A_1)) = A_1
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_61,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_30])).

tff(c_135,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_141,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_135])).

tff(c_145,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_61,c_28,c_141])).

tff(c_96,plain,(
    ! [A_42,B_43,C_44] :
      ( v1_funct_1(k2_tops_2(A_42,B_43,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_99,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_102,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_99])).

tff(c_155,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102])).

tff(c_103,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_2(k2_tops_2(A_45,B_46,C_47),B_46,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_105,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_103])).

tff(c_108,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_105])).

tff(c_154,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_108])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_tops_2(A_13,B_14,C_15),k1_zfmisc_1(k2_zfmisc_1(B_14,A_13)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_14])).

tff(c_164,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_66,c_160])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_tops_2(A_10,B_11,C_12) = k2_funct_1(C_12)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(A_10,B_11,C_12) != B_11
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_164,c_12])).

tff(c_184,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_154,c_168])).

tff(c_231,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_288,plain,(
    ! [B_73,A_74,C_75] :
      ( k2_relset_1(u1_struct_0(B_73),u1_struct_0(A_74),k2_tops_2(u1_struct_0(A_74),u1_struct_0(B_73),C_75)) = k2_struct_0(A_74)
      | ~ v2_funct_1(C_75)
      | k2_relset_1(u1_struct_0(A_74),u1_struct_0(B_73),C_75) != k2_struct_0(B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0(B_73))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_74),u1_struct_0(B_73))
      | ~ v1_funct_1(C_75)
      | ~ l1_struct_0(B_73)
      | v2_struct_0(B_73)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_309,plain,(
    ! [A_74,C_75] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_74),k2_tops_2(u1_struct_0(A_74),u1_struct_0('#skF_2'),C_75)) = k2_struct_0(A_74)
      | ~ v2_funct_1(C_75)
      | k2_relset_1(u1_struct_0(A_74),u1_struct_0('#skF_2'),C_75) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_74),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_288])).

tff(c_330,plain,(
    ! [A_74,C_75] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_74),k2_tops_2(u1_struct_0(A_74),k2_struct_0('#skF_2'),C_75)) = k2_struct_0(A_74)
      | ~ v2_funct_1(C_75)
      | k2_relset_1(u1_struct_0(A_74),k2_struct_0('#skF_2'),C_75) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_74),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_50,c_50,c_309])).

tff(c_366,plain,(
    ! [A_83,C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_83),k2_tops_2(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84)) = k2_struct_0(A_83)
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0(A_83),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_330])).

tff(c_378,plain,(
    ! [C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_366])).

tff(c_521,plain,(
    ! [C_97] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_97)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_97,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_51,c_378])).

tff(c_530,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_521])).

tff(c_534,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_66,c_61,c_28,c_530])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_534])).

tff(c_537,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_559,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_205,plain,(
    ! [A_61,B_62,C_63] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_61),u1_struct_0(B_62),C_63))
      | ~ v2_funct_1(C_63)
      | k2_relset_1(u1_struct_0(A_61),u1_struct_0(B_62),C_63) != k2_struct_0(B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_63,u1_struct_0(A_61),u1_struct_0(B_62))
      | ~ v1_funct_1(C_63)
      | ~ l1_struct_0(B_62)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_221,plain,(
    ! [A_61,C_63] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_61),u1_struct_0('#skF_2'),C_63))
      | ~ v2_funct_1(C_63)
      | k2_relset_1(u1_struct_0(A_61),u1_struct_0('#skF_2'),C_63) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_63,u1_struct_0(A_61),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_63)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_205])).

tff(c_707,plain,(
    ! [A_119,C_120] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_119),k2_struct_0('#skF_2'),C_120))
      | ~ v2_funct_1(C_120)
      | k2_relset_1(u1_struct_0(A_119),k2_struct_0('#skF_2'),C_120) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_119),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_120,u1_struct_0(A_119),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_120)
      | ~ l1_struct_0(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_50,c_221])).

tff(c_714,plain,(
    ! [C_120] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_120))
      | ~ v2_funct_1(C_120)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_120) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_120,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_120)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_707])).

tff(c_723,plain,(
    ! [C_121] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_121))
      | ~ v2_funct_1(C_121)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_121) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_121,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_714])).

tff(c_730,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_723])).

tff(c_734,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_61,c_28,c_145,c_730])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_734])).

tff(c_737,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_95,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_51,c_51,c_50,c_50,c_50,c_26])).

tff(c_156,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_95])).

tff(c_793,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_156])).

tff(c_849,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_793])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36,c_28,c_94,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.30/1.52  
% 3.30/1.52  %Foreground sorts:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Background operators:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Foreground operators:
% 3.30/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.30/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.52  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.30/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.30/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.30/1.52  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.30/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.52  
% 3.30/1.54  tff(f_144, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.30/1.54  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.30/1.54  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.54  tff(f_53, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.30/1.54  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.30/1.54  tff(f_69, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.30/1.54  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.30/1.54  tff(f_104, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.30/1.54  tff(f_122, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.30/1.54  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_43, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.54  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_43])).
% 3.30/1.54  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_50, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_43])).
% 3.30/1.54  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_32])).
% 3.30/1.54  tff(c_67, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_67])).
% 3.30/1.54  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_60, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_34])).
% 3.30/1.54  tff(c_89, plain, (![A_39, B_40, D_41]: (r2_funct_2(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_41, A_39, B_40) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_91, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_89])).
% 3.30/1.54  tff(c_94, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_91])).
% 3.30/1.54  tff(c_2, plain, (![A_1]: (k2_funct_1(k2_funct_1(A_1))=A_1 | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.54  tff(c_30, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_61, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_30])).
% 3.30/1.54  tff(c_135, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.54  tff(c_141, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_135])).
% 3.30/1.54  tff(c_145, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_61, c_28, c_141])).
% 3.30/1.54  tff(c_96, plain, (![A_42, B_43, C_44]: (v1_funct_1(k2_tops_2(A_42, B_43, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.54  tff(c_99, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_96])).
% 3.30/1.54  tff(c_102, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_99])).
% 3.30/1.54  tff(c_155, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102])).
% 3.30/1.54  tff(c_103, plain, (![A_45, B_46, C_47]: (v1_funct_2(k2_tops_2(A_45, B_46, C_47), B_46, A_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.54  tff(c_105, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_103])).
% 3.30/1.54  tff(c_108, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_105])).
% 3.30/1.54  tff(c_154, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_108])).
% 3.30/1.54  tff(c_14, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_tops_2(A_13, B_14, C_15), k1_zfmisc_1(k2_zfmisc_1(B_14, A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.54  tff(c_160, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_14])).
% 3.30/1.54  tff(c_164, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_66, c_160])).
% 3.30/1.54  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_tops_2(A_10, B_11, C_12)=k2_funct_1(C_12) | ~v2_funct_1(C_12) | k2_relset_1(A_10, B_11, C_12)!=B_11 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.54  tff(c_168, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_164, c_12])).
% 3.30/1.54  tff(c_184, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_154, c_168])).
% 3.30/1.54  tff(c_231, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_184])).
% 3.30/1.54  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_288, plain, (![B_73, A_74, C_75]: (k2_relset_1(u1_struct_0(B_73), u1_struct_0(A_74), k2_tops_2(u1_struct_0(A_74), u1_struct_0(B_73), C_75))=k2_struct_0(A_74) | ~v2_funct_1(C_75) | k2_relset_1(u1_struct_0(A_74), u1_struct_0(B_73), C_75)!=k2_struct_0(B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), u1_struct_0(B_73)))) | ~v1_funct_2(C_75, u1_struct_0(A_74), u1_struct_0(B_73)) | ~v1_funct_1(C_75) | ~l1_struct_0(B_73) | v2_struct_0(B_73) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.30/1.54  tff(c_309, plain, (![A_74, C_75]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_74), k2_tops_2(u1_struct_0(A_74), u1_struct_0('#skF_2'), C_75))=k2_struct_0(A_74) | ~v2_funct_1(C_75) | k2_relset_1(u1_struct_0(A_74), u1_struct_0('#skF_2'), C_75)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0(A_74), u1_struct_0('#skF_2')) | ~v1_funct_1(C_75) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_50, c_288])).
% 3.30/1.54  tff(c_330, plain, (![A_74, C_75]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_74), k2_tops_2(u1_struct_0(A_74), k2_struct_0('#skF_2'), C_75))=k2_struct_0(A_74) | ~v2_funct_1(C_75) | k2_relset_1(u1_struct_0(A_74), k2_struct_0('#skF_2'), C_75)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0(A_74), k2_struct_0('#skF_2')) | ~v1_funct_1(C_75) | v2_struct_0('#skF_2') | ~l1_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_50, c_50, c_309])).
% 3.30/1.54  tff(c_366, plain, (![A_83, C_84]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_83), k2_tops_2(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84))=k2_struct_0(A_83) | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0(A_83), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0(A_83))), inference(negUnitSimplification, [status(thm)], [c_40, c_330])).
% 3.30/1.54  tff(c_378, plain, (![C_84]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84))=k2_struct_0('#skF_1') | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_366])).
% 3.30/1.54  tff(c_521, plain, (![C_97]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97))=k2_struct_0('#skF_1') | ~v2_funct_1(C_97) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_97, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51, c_51, c_51, c_51, c_378])).
% 3.30/1.54  tff(c_530, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_521])).
% 3.30/1.54  tff(c_534, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_66, c_61, c_28, c_530])).
% 3.30/1.54  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_534])).
% 3.30/1.54  tff(c_537, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_184])).
% 3.30/1.54  tff(c_559, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_537])).
% 3.30/1.54  tff(c_205, plain, (![A_61, B_62, C_63]: (v2_funct_1(k2_tops_2(u1_struct_0(A_61), u1_struct_0(B_62), C_63)) | ~v2_funct_1(C_63) | k2_relset_1(u1_struct_0(A_61), u1_struct_0(B_62), C_63)!=k2_struct_0(B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(B_62)))) | ~v1_funct_2(C_63, u1_struct_0(A_61), u1_struct_0(B_62)) | ~v1_funct_1(C_63) | ~l1_struct_0(B_62) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.54  tff(c_221, plain, (![A_61, C_63]: (v2_funct_1(k2_tops_2(u1_struct_0(A_61), u1_struct_0('#skF_2'), C_63)) | ~v2_funct_1(C_63) | k2_relset_1(u1_struct_0(A_61), u1_struct_0('#skF_2'), C_63)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_63, u1_struct_0(A_61), u1_struct_0('#skF_2')) | ~v1_funct_1(C_63) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_50, c_205])).
% 3.30/1.54  tff(c_707, plain, (![A_119, C_120]: (v2_funct_1(k2_tops_2(u1_struct_0(A_119), k2_struct_0('#skF_2'), C_120)) | ~v2_funct_1(C_120) | k2_relset_1(u1_struct_0(A_119), k2_struct_0('#skF_2'), C_120)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_119), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_120, u1_struct_0(A_119), k2_struct_0('#skF_2')) | ~v1_funct_1(C_120) | ~l1_struct_0(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_50, c_221])).
% 3.30/1.54  tff(c_714, plain, (![C_120]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_120)) | ~v2_funct_1(C_120) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_120)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_120, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_120) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_707])).
% 3.30/1.54  tff(c_723, plain, (![C_121]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_121)) | ~v2_funct_1(C_121) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_121)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_121, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_121))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51, c_51, c_51, c_714])).
% 3.30/1.54  tff(c_730, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_723])).
% 3.30/1.54  tff(c_734, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_61, c_28, c_145, c_730])).
% 3.30/1.54  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_734])).
% 3.30/1.54  tff(c_737, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_537])).
% 3.30/1.54  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.54  tff(c_95, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_51, c_51, c_50, c_50, c_50, c_26])).
% 3.30/1.54  tff(c_156, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_95])).
% 3.30/1.54  tff(c_793, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_156])).
% 3.30/1.54  tff(c_849, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_793])).
% 3.30/1.54  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_36, c_28, c_94, c_849])).
% 3.30/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  Inference rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Ref     : 0
% 3.30/1.54  #Sup     : 161
% 3.30/1.54  #Fact    : 0
% 3.30/1.54  #Define  : 0
% 3.30/1.54  #Split   : 2
% 3.30/1.54  #Chain   : 0
% 3.30/1.54  #Close   : 0
% 3.30/1.54  
% 3.30/1.54  Ordering : KBO
% 3.30/1.54  
% 3.30/1.54  Simplification rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Subsume      : 7
% 3.30/1.54  #Demod        : 475
% 3.30/1.54  #Tautology    : 52
% 3.30/1.54  #SimpNegUnit  : 10
% 3.30/1.54  #BackRed      : 8
% 3.30/1.54  
% 3.30/1.54  #Partial instantiations: 0
% 3.30/1.54  #Strategies tried      : 1
% 3.30/1.54  
% 3.30/1.54  Timing (in seconds)
% 3.30/1.54  ----------------------
% 3.57/1.54  Preprocessing        : 0.34
% 3.57/1.54  Parsing              : 0.18
% 3.57/1.54  CNF conversion       : 0.02
% 3.57/1.54  Main loop            : 0.43
% 3.57/1.54  Inferencing          : 0.14
% 3.57/1.54  Reduction            : 0.16
% 3.57/1.54  Demodulation         : 0.13
% 3.57/1.54  BG Simplification    : 0.03
% 3.57/1.54  Subsumption          : 0.07
% 3.57/1.54  Abstraction          : 0.03
% 3.57/1.54  MUC search           : 0.00
% 3.57/1.54  Cooper               : 0.00
% 3.57/1.54  Total                : 0.81
% 3.57/1.54  Index Insertion      : 0.00
% 3.57/1.54  Index Deletion       : 0.00
% 3.57/1.54  Index Matching       : 0.00
% 3.57/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
