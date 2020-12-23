%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 384 expanded)
%              Number of leaves         :   38 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 (1442 expanded)
%              Number of equality atoms :   19 ( 186 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( v1_compts_1(A)
                    & v8_pre_topc(B)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v5_pre_topc(C,A,B) )
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( v4_pre_topc(D,A)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                 => ( ( v5_pre_topc(D,A,C)
                      & k2_relset_1(u1_struct_0(A),u1_struct_0(C),D) = k2_struct_0(C)
                      & v2_compts_1(B,A) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(A),u1_struct_0(C),D,B),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_80,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_79,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_40])).

tff(c_94,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_91,c_94])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_30])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_81,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42])).

tff(c_92,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_81])).

tff(c_32,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_113,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_34])).

tff(c_38,plain,(
    v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_18,plain,(
    ! [A_11] :
      ( v2_compts_1(k2_struct_0(A_11),A_11)
      | ~ v1_compts_1(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_28,plain,(
    v4_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_108,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_94])).

tff(c_229,plain,(
    ! [C_81,A_82,B_83] :
      ( v2_compts_1(C_81,A_82)
      | ~ v4_pre_topc(C_81,A_82)
      | ~ r1_tarski(C_81,B_83)
      | ~ v2_compts_1(B_83,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_279,plain,(
    ! [A_87] :
      ( v2_compts_1('#skF_4',A_87)
      | ~ v4_pre_topc('#skF_4',A_87)
      | ~ v2_compts_1(k2_struct_0('#skF_1'),A_87)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_108,c_229])).

tff(c_285,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_279])).

tff(c_291,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_55,c_86,c_80,c_28,c_285])).

tff(c_294,plain,(
    ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_297,plain,
    ( ~ v1_compts_1('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_294])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_297])).

tff(c_302,plain,(
    v2_compts_1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_324,plain,(
    ! [A_94,C_95,D_96,B_97] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_94),u1_struct_0(C_95),D_96,B_97),C_95)
      | ~ v2_compts_1(B_97,A_94)
      | k2_relset_1(u1_struct_0(A_94),u1_struct_0(C_95),D_96) != k2_struct_0(C_95)
      | ~ v5_pre_topc(D_96,A_94,C_95)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(C_95))))
      | ~ v1_funct_2(D_96,u1_struct_0(A_94),u1_struct_0(C_95))
      | ~ v1_funct_1(D_96)
      | ~ l1_pre_topc(C_95)
      | v2_struct_0(C_95)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_338,plain,(
    ! [A_94,D_96,B_97] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_94),u1_struct_0('#skF_2'),D_96,B_97),'#skF_2')
      | ~ v2_compts_1(B_97,A_94)
      | k2_relset_1(u1_struct_0(A_94),u1_struct_0('#skF_2'),D_96) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_96,A_94,'#skF_2')
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_96,u1_struct_0(A_94),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_96)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_324])).

tff(c_351,plain,(
    ! [A_94,D_96,B_97] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_94),k2_struct_0('#skF_2'),D_96,B_97),'#skF_2')
      | ~ v2_compts_1(B_97,A_94)
      | k2_relset_1(u1_struct_0(A_94),k2_struct_0('#skF_2'),D_96) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_96,A_94,'#skF_2')
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_96,u1_struct_0(A_94),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_96)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_79,c_79,c_338])).

tff(c_359,plain,(
    ! [A_98,D_99,B_100] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_98),k2_struct_0('#skF_2'),D_99,B_100),'#skF_2')
      | ~ v2_compts_1(B_100,A_98)
      | k2_relset_1(u1_struct_0(A_98),k2_struct_0('#skF_2'),D_99) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_99,A_98,'#skF_2')
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_99,u1_struct_0(A_98),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_351])).

tff(c_483,plain,(
    ! [A_122,A_123,B_124] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_122),k2_struct_0('#skF_2'),A_123,B_124),'#skF_2')
      | ~ v2_compts_1(B_124,A_122)
      | k2_relset_1(u1_struct_0(A_122),k2_struct_0('#skF_2'),A_123) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_123,A_122,'#skF_2')
      | ~ v1_funct_2(A_123,u1_struct_0(A_122),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ r1_tarski(A_123,k2_zfmisc_1(u1_struct_0(A_122),k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_486,plain,(
    ! [A_123,B_124] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_123,B_124),'#skF_2')
      | ~ v2_compts_1(B_124,'#skF_1')
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_123) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_123,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_123,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_123,k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_483])).

tff(c_1024,plain,(
    ! [A_226,B_227] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_226,B_227),'#skF_2')
      | ~ v2_compts_1(B_227,'#skF_1')
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_226) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_226,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_226,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_226,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52,c_80,c_80,c_80,c_486])).

tff(c_124,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( m1_subset_1(k7_relset_1(A_60,B_61,C_62,D_63),k1_zfmisc_1(B_61))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r1_tarski(k7_relset_1(A_64,B_65,C_66,D_67),B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_143,plain,(
    ! [D_67] : r1_tarski(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_67),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_129])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_147,plain,(
    ! [B_72,A_73] :
      ( v4_pre_topc(B_72,A_73)
      | ~ v2_compts_1(B_72,A_73)
      | ~ v8_pre_topc(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_161,plain,(
    ! [B_72] :
      ( v4_pre_topc(B_72,'#skF_2')
      | ~ v2_compts_1(B_72,'#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_147])).

tff(c_173,plain,(
    ! [B_74] :
      ( v4_pre_topc(B_74,'#skF_2')
      | ~ v2_compts_1(B_74,'#skF_2')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_161])).

tff(c_197,plain,(
    ! [A_75] :
      ( v4_pre_topc(A_75,'#skF_2')
      | ~ v2_compts_1(A_75,'#skF_2')
      | ~ r1_tarski(A_75,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_274,plain,(
    ! [D_86] :
      ( v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_86),'#skF_2')
      | ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_86),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_143,c_197])).

tff(c_26,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_26])).

tff(c_278,plain,(
    ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_274,c_118])).

tff(c_1027,plain,
    ( ~ v2_compts_1('#skF_4','#skF_1')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1024,c_278])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_86,c_44,c_92,c_32,c_113,c_302,c_1027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.77  
% 4.17/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.77  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.77  
% 4.17/1.77  %Foreground sorts:
% 4.17/1.77  
% 4.17/1.77  
% 4.17/1.77  %Background operators:
% 4.17/1.77  
% 4.17/1.77  
% 4.17/1.77  %Foreground operators:
% 4.17/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.17/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.17/1.77  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.17/1.77  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.17/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.17/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.77  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.17/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.17/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.17/1.77  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.17/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.17/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.77  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.17/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.17/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.17/1.77  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 4.17/1.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.17/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.17/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.77  
% 4.30/1.79  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 4.30/1.79  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.30/1.79  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.30/1.79  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.30/1.79  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 4.30/1.79  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.30/1.79  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.30/1.79  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 4.30/1.79  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_compts_1)).
% 4.30/1.79  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.30/1.79  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.30/1.79  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.79  tff(c_67, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.30/1.79  tff(c_72, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_14, c_67])).
% 4.30/1.79  tff(c_80, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_72])).
% 4.30/1.79  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_79, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_72])).
% 4.30/1.79  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_40])).
% 4.30/1.79  tff(c_94, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.30/1.79  tff(c_109, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_91, c_94])).
% 4.30/1.79  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_30])).
% 4.30/1.79  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_81, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42])).
% 4.30/1.79  tff(c_92, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_81])).
% 4.30/1.79  tff(c_32, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_113, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_34])).
% 4.30/1.79  tff(c_38, plain, (v1_compts_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_18, plain, (![A_11]: (v2_compts_1(k2_struct_0(A_11), A_11) | ~v1_compts_1(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.30/1.79  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.30/1.79  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.30/1.79  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.30/1.79  tff(c_28, plain, (v4_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_108, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_94])).
% 4.30/1.79  tff(c_229, plain, (![C_81, A_82, B_83]: (v2_compts_1(C_81, A_82) | ~v4_pre_topc(C_81, A_82) | ~r1_tarski(C_81, B_83) | ~v2_compts_1(B_83, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.30/1.79  tff(c_279, plain, (![A_87]: (v2_compts_1('#skF_4', A_87) | ~v4_pre_topc('#skF_4', A_87) | ~v2_compts_1(k2_struct_0('#skF_1'), A_87) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(resolution, [status(thm)], [c_108, c_229])).
% 4.30/1.79  tff(c_285, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v4_pre_topc('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_279])).
% 4.30/1.79  tff(c_291, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_55, c_86, c_80, c_28, c_285])).
% 4.30/1.79  tff(c_294, plain, (~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_291])).
% 4.30/1.79  tff(c_297, plain, (~v1_compts_1('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_294])).
% 4.30/1.79  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_297])).
% 4.30/1.79  tff(c_302, plain, (v2_compts_1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_291])).
% 4.30/1.79  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.30/1.79  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_324, plain, (![A_94, C_95, D_96, B_97]: (v2_compts_1(k7_relset_1(u1_struct_0(A_94), u1_struct_0(C_95), D_96, B_97), C_95) | ~v2_compts_1(B_97, A_94) | k2_relset_1(u1_struct_0(A_94), u1_struct_0(C_95), D_96)!=k2_struct_0(C_95) | ~v5_pre_topc(D_96, A_94, C_95) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94), u1_struct_0(C_95)))) | ~v1_funct_2(D_96, u1_struct_0(A_94), u1_struct_0(C_95)) | ~v1_funct_1(D_96) | ~l1_pre_topc(C_95) | v2_struct_0(C_95) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.30/1.79  tff(c_338, plain, (![A_94, D_96, B_97]: (v2_compts_1(k7_relset_1(u1_struct_0(A_94), u1_struct_0('#skF_2'), D_96, B_97), '#skF_2') | ~v2_compts_1(B_97, A_94) | k2_relset_1(u1_struct_0(A_94), u1_struct_0('#skF_2'), D_96)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_96, A_94, '#skF_2') | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_96, u1_struct_0(A_94), u1_struct_0('#skF_2')) | ~v1_funct_1(D_96) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_79, c_324])).
% 4.30/1.79  tff(c_351, plain, (![A_94, D_96, B_97]: (v2_compts_1(k7_relset_1(u1_struct_0(A_94), k2_struct_0('#skF_2'), D_96, B_97), '#skF_2') | ~v2_compts_1(B_97, A_94) | k2_relset_1(u1_struct_0(A_94), k2_struct_0('#skF_2'), D_96)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_96, A_94, '#skF_2') | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_96, u1_struct_0(A_94), k2_struct_0('#skF_2')) | ~v1_funct_1(D_96) | v2_struct_0('#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_79, c_79, c_338])).
% 4.30/1.79  tff(c_359, plain, (![A_98, D_99, B_100]: (v2_compts_1(k7_relset_1(u1_struct_0(A_98), k2_struct_0('#skF_2'), D_99, B_100), '#skF_2') | ~v2_compts_1(B_100, A_98) | k2_relset_1(u1_struct_0(A_98), k2_struct_0('#skF_2'), D_99)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_99, A_98, '#skF_2') | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_99, u1_struct_0(A_98), k2_struct_0('#skF_2')) | ~v1_funct_1(D_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(negUnitSimplification, [status(thm)], [c_50, c_351])).
% 4.30/1.79  tff(c_483, plain, (![A_122, A_123, B_124]: (v2_compts_1(k7_relset_1(u1_struct_0(A_122), k2_struct_0('#skF_2'), A_123, B_124), '#skF_2') | ~v2_compts_1(B_124, A_122) | k2_relset_1(u1_struct_0(A_122), k2_struct_0('#skF_2'), A_123)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_123, A_122, '#skF_2') | ~v1_funct_2(A_123, u1_struct_0(A_122), k2_struct_0('#skF_2')) | ~v1_funct_1(A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~r1_tarski(A_123, k2_zfmisc_1(u1_struct_0(A_122), k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_359])).
% 4.30/1.79  tff(c_486, plain, (![A_123, B_124]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_123, B_124), '#skF_2') | ~v2_compts_1(B_124, '#skF_1') | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_123)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_123, '#skF_1', '#skF_2') | ~v1_funct_2(A_123, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_123, k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_80, c_483])).
% 4.30/1.79  tff(c_1024, plain, (![A_226, B_227]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_226, B_227), '#skF_2') | ~v2_compts_1(B_227, '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_226)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_226, '#skF_1', '#skF_2') | ~v1_funct_2(A_226, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_226) | ~m1_subset_1(B_227, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_226, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52, c_80, c_80, c_80, c_486])).
% 4.30/1.79  tff(c_124, plain, (![A_60, B_61, C_62, D_63]: (m1_subset_1(k7_relset_1(A_60, B_61, C_62, D_63), k1_zfmisc_1(B_61)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.30/1.79  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.30/1.79  tff(c_129, plain, (![A_64, B_65, C_66, D_67]: (r1_tarski(k7_relset_1(A_64, B_65, C_66, D_67), B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(resolution, [status(thm)], [c_124, c_6])).
% 4.30/1.79  tff(c_143, plain, (![D_67]: (r1_tarski(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_67), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_91, c_129])).
% 4.30/1.79  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_36, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_147, plain, (![B_72, A_73]: (v4_pre_topc(B_72, A_73) | ~v2_compts_1(B_72, A_73) | ~v8_pre_topc(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.30/1.79  tff(c_161, plain, (![B_72]: (v4_pre_topc(B_72, '#skF_2') | ~v2_compts_1(B_72, '#skF_2') | ~v8_pre_topc('#skF_2') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_147])).
% 4.30/1.79  tff(c_173, plain, (![B_74]: (v4_pre_topc(B_74, '#skF_2') | ~v2_compts_1(B_74, '#skF_2') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_161])).
% 4.30/1.79  tff(c_197, plain, (![A_75]: (v4_pre_topc(A_75, '#skF_2') | ~v2_compts_1(A_75, '#skF_2') | ~r1_tarski(A_75, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_173])).
% 4.30/1.79  tff(c_274, plain, (![D_86]: (v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_86), '#skF_2') | ~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_86), '#skF_2'))), inference(resolution, [status(thm)], [c_143, c_197])).
% 4.30/1.79  tff(c_26, plain, (~v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.30/1.79  tff(c_118, plain, (~v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_26])).
% 4.30/1.79  tff(c_278, plain, (~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_274, c_118])).
% 4.30/1.79  tff(c_1027, plain, (~v2_compts_1('#skF_4', '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1024, c_278])).
% 4.30/1.79  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_86, c_44, c_92, c_32, c_113, c_302, c_1027])).
% 4.30/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.79  
% 4.30/1.79  Inference rules
% 4.30/1.79  ----------------------
% 4.30/1.79  #Ref     : 0
% 4.30/1.79  #Sup     : 186
% 4.30/1.79  #Fact    : 0
% 4.30/1.79  #Define  : 0
% 4.30/1.79  #Split   : 7
% 4.30/1.79  #Chain   : 0
% 4.30/1.79  #Close   : 0
% 4.30/1.79  
% 4.30/1.79  Ordering : KBO
% 4.30/1.79  
% 4.30/1.79  Simplification rules
% 4.30/1.79  ----------------------
% 4.30/1.79  #Subsume      : 64
% 4.30/1.79  #Demod        : 546
% 4.30/1.79  #Tautology    : 20
% 4.30/1.79  #SimpNegUnit  : 6
% 4.30/1.79  #BackRed      : 2
% 4.30/1.79  
% 4.30/1.79  #Partial instantiations: 0
% 4.30/1.79  #Strategies tried      : 1
% 4.30/1.79  
% 4.30/1.79  Timing (in seconds)
% 4.30/1.79  ----------------------
% 4.30/1.79  Preprocessing        : 0.40
% 4.30/1.79  Parsing              : 0.20
% 4.30/1.79  CNF conversion       : 0.03
% 4.30/1.79  Main loop            : 0.53
% 4.30/1.79  Inferencing          : 0.19
% 4.30/1.79  Reduction            : 0.20
% 4.30/1.79  Demodulation         : 0.15
% 4.30/1.79  BG Simplification    : 0.02
% 4.30/1.79  Subsumption          : 0.09
% 4.30/1.79  Abstraction          : 0.03
% 4.30/1.79  MUC search           : 0.00
% 4.30/1.79  Cooper               : 0.00
% 4.30/1.79  Total                : 0.97
% 4.30/1.79  Index Insertion      : 0.00
% 4.30/1.79  Index Deletion       : 0.00
% 4.30/1.80  Index Matching       : 0.00
% 4.30/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
