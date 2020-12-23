%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 429 expanded)
%              Number of leaves         :   41 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  246 (1621 expanded)
%              Number of equality atoms :   18 ( 199 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_160,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_18,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_84,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_34])).

tff(c_42,plain,(
    v1_compts_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_22,plain,(
    ! [A_20] :
      ( v2_compts_1(k2_struct_0(A_20),A_20)
      | ~ v1_compts_1(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_32,plain,(
    v4_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_112,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_1'(A_74,B_75,C_76),B_75)
      | r1_tarski(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_201,plain,(
    ! [A_87,B_88,C_89,A_90] :
      ( r2_hidden('#skF_1'(A_87,B_88,C_89),A_90)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_90))
      | r1_tarski(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_214,plain,(
    ! [B_94,A_95,A_96] :
      ( ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | r1_tarski(B_94,A_95)
      | ~ m1_subset_1(A_95,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_229,plain,(
    ! [A_96] :
      ( r1_tarski('#skF_5',k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(A_96))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_90,c_214])).

tff(c_233,plain,(
    ! [A_97] :
      ( ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(A_97))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_97)) ) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_237,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_59,c_233])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_237])).

tff(c_242,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_26,plain,(
    ! [C_30,A_24,B_28] :
      ( v2_compts_1(C_30,A_24)
      | ~ v4_pre_topc(C_30,A_24)
      | ~ r1_tarski(C_30,B_28)
      | ~ v2_compts_1(B_28,A_24)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_518,plain,(
    ! [A_157] :
      ( v2_compts_1('#skF_5',A_157)
      | ~ v4_pre_topc('#skF_5',A_157)
      | ~ v2_compts_1(k2_struct_0('#skF_2'),A_157)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_242,c_26])).

tff(c_521,plain,
    ( v2_compts_1('#skF_5','#skF_2')
    | ~ v4_pre_topc('#skF_5','#skF_2')
    | ~ v2_compts_1(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_518])).

tff(c_526,plain,
    ( v2_compts_1('#skF_5','#skF_2')
    | ~ v2_compts_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_59,c_90,c_84,c_32,c_521])).

tff(c_529,plain,(
    ~ v2_compts_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_532,plain,
    ( ~ v1_compts_1('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_529])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_532])).

tff(c_537,plain,(
    v2_compts_1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_83,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_85,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46])).

tff(c_100,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85])).

tff(c_36,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_95,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_38])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_101,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_44])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_279,plain,(
    ! [A_102,C_103,D_104,B_105] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_102),u1_struct_0(C_103),D_104,B_105),C_103)
      | ~ v2_compts_1(B_105,A_102)
      | k2_relset_1(u1_struct_0(A_102),u1_struct_0(C_103),D_104) != k2_struct_0(C_103)
      | ~ v5_pre_topc(D_104,A_102,C_103)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(C_103))))
      | ~ v1_funct_2(D_104,u1_struct_0(A_102),u1_struct_0(C_103))
      | ~ v1_funct_1(D_104)
      | ~ l1_pre_topc(C_103)
      | v2_struct_0(C_103)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_293,plain,(
    ! [A_102,D_104,B_105] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_102),u1_struct_0('#skF_3'),D_104,B_105),'#skF_3')
      | ~ v2_compts_1(B_105,A_102)
      | k2_relset_1(u1_struct_0(A_102),u1_struct_0('#skF_3'),D_104) != k2_struct_0('#skF_3')
      | ~ v5_pre_topc(D_104,A_102,'#skF_3')
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),k2_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_104,u1_struct_0(A_102),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_104)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_279])).

tff(c_306,plain,(
    ! [A_102,D_104,B_105] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_102),k2_struct_0('#skF_3'),D_104,B_105),'#skF_3')
      | ~ v2_compts_1(B_105,A_102)
      | k2_relset_1(u1_struct_0(A_102),k2_struct_0('#skF_3'),D_104) != k2_struct_0('#skF_3')
      | ~ v5_pre_topc(D_104,A_102,'#skF_3')
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),k2_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_104,u1_struct_0(A_102),k2_struct_0('#skF_3'))
      | ~ v1_funct_1(D_104)
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_83,c_83,c_293])).

tff(c_315,plain,(
    ! [A_109,D_110,B_111] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_109),k2_struct_0('#skF_3'),D_110,B_111),'#skF_3')
      | ~ v2_compts_1(B_111,A_109)
      | k2_relset_1(u1_struct_0(A_109),k2_struct_0('#skF_3'),D_110) != k2_struct_0('#skF_3')
      | ~ v5_pre_topc(D_110,A_109,'#skF_3')
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),k2_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_110,u1_struct_0(A_109),k2_struct_0('#skF_3'))
      | ~ v1_funct_1(D_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_306])).

tff(c_323,plain,(
    ! [D_110,B_111] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3'),D_110,B_111),'#skF_3')
      | ~ v2_compts_1(B_111,'#skF_2')
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3'),D_110) != k2_struct_0('#skF_3')
      | ~ v5_pre_topc(D_110,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_110,u1_struct_0('#skF_2'),k2_struct_0('#skF_3'))
      | ~ v1_funct_1(D_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_315])).

tff(c_1084,plain,(
    ! [D_359,B_360] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),D_359,B_360),'#skF_3')
      | ~ v2_compts_1(B_360,'#skF_2')
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),D_359) != k2_struct_0('#skF_3')
      | ~ v5_pre_topc(D_359,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_359,k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
      | ~ v1_funct_1(D_359)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_84,c_84,c_84,c_84,c_323])).

tff(c_1092,plain,(
    ! [B_360] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',B_360),'#skF_3')
      | ~ v2_compts_1(B_360,'#skF_2')
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_101,c_1084])).

tff(c_1102,plain,(
    ! [B_361] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',B_361),'#skF_3')
      | ~ v2_compts_1(B_361,'#skF_2')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_100,c_36,c_95,c_1092])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( m1_subset_1(k7_relset_1(A_14,B_15,C_16,D_17),k1_zfmisc_1(B_15))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    v8_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_138,plain,(
    ! [B_80,A_81] :
      ( v4_pre_topc(B_80,A_81)
      | ~ v2_compts_1(B_80,A_81)
      | ~ v8_pre_topc(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_148,plain,(
    ! [B_80] :
      ( v4_pre_topc(B_80,'#skF_3')
      | ~ v2_compts_1(B_80,'#skF_3')
      | ~ v8_pre_topc('#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_138])).

tff(c_165,plain,(
    ! [B_85] :
      ( v4_pre_topc(B_85,'#skF_3')
      | ~ v2_compts_1(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_148])).

tff(c_263,plain,(
    ! [A_99,C_100,D_101] :
      ( v4_pre_topc(k7_relset_1(A_99,k2_struct_0('#skF_3'),C_100,D_101),'#skF_3')
      | ~ v2_compts_1(k7_relset_1(A_99,k2_struct_0('#skF_3'),C_100,D_101),'#skF_3')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,k2_struct_0('#skF_3')))) ) ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_309,plain,(
    ! [D_106] :
      ( v4_pre_topc(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',D_106),'#skF_3')
      | ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',D_106),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_263])).

tff(c_30,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_108,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_30])).

tff(c_313,plain,(
    ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_309,c_108])).

tff(c_1105,plain,
    ( ~ v2_compts_1('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1102,c_313])).

tff(c_1109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_537,c_1105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  
% 4.54/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.54/1.82  
% 4.54/1.82  %Foreground sorts:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Background operators:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Foreground operators:
% 4.54/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.54/1.82  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.54/1.82  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.54/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.54/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.54/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.54/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.54/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.82  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.54/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.54/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.54/1.82  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 4.54/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.54/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.54/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.82  
% 4.67/1.85  tff(f_160, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_compts_1)).
% 4.67/1.85  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.67/1.85  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.67/1.85  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_compts_1)).
% 4.67/1.85  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.67/1.85  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.67/1.85  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 4.67/1.85  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.67/1.85  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 4.67/1.85  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_compts_1)).
% 4.67/1.85  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.67/1.85  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 4.67/1.85  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_18, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.67/1.85  tff(c_71, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.85  tff(c_76, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_18, c_71])).
% 4.67/1.85  tff(c_84, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_76])).
% 4.67/1.85  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_34])).
% 4.67/1.85  tff(c_42, plain, (v1_compts_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_22, plain, (![A_20]: (v2_compts_1(k2_struct_0(A_20), A_20) | ~v1_compts_1(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.67/1.85  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.67/1.85  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.85  tff(c_59, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.67/1.85  tff(c_32, plain, (v4_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_112, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_1'(A_74, B_75, C_76), B_75) | r1_tarski(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.67/1.85  tff(c_6, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.67/1.85  tff(c_201, plain, (![A_87, B_88, C_89, A_90]: (r2_hidden('#skF_1'(A_87, B_88, C_89), A_90) | ~m1_subset_1(B_88, k1_zfmisc_1(A_90)) | r1_tarski(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_112, c_6])).
% 4.67/1.85  tff(c_8, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.67/1.85  tff(c_214, plain, (![B_94, A_95, A_96]: (~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | r1_tarski(B_94, A_95) | ~m1_subset_1(A_95, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_201, c_8])).
% 4.67/1.85  tff(c_229, plain, (![A_96]: (r1_tarski('#skF_5', k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(A_96)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_90, c_214])).
% 4.67/1.85  tff(c_233, plain, (![A_97]: (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(A_97)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_97)))), inference(splitLeft, [status(thm)], [c_229])).
% 4.67/1.85  tff(c_237, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_59, c_233])).
% 4.67/1.85  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_237])).
% 4.67/1.85  tff(c_242, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_229])).
% 4.67/1.85  tff(c_26, plain, (![C_30, A_24, B_28]: (v2_compts_1(C_30, A_24) | ~v4_pre_topc(C_30, A_24) | ~r1_tarski(C_30, B_28) | ~v2_compts_1(B_28, A_24) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.67/1.85  tff(c_518, plain, (![A_157]: (v2_compts_1('#skF_5', A_157) | ~v4_pre_topc('#skF_5', A_157) | ~v2_compts_1(k2_struct_0('#skF_2'), A_157) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(resolution, [status(thm)], [c_242, c_26])).
% 4.67/1.85  tff(c_521, plain, (v2_compts_1('#skF_5', '#skF_2') | ~v4_pre_topc('#skF_5', '#skF_2') | ~v2_compts_1(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_518])).
% 4.67/1.85  tff(c_526, plain, (v2_compts_1('#skF_5', '#skF_2') | ~v2_compts_1(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_59, c_90, c_84, c_32, c_521])).
% 4.67/1.85  tff(c_529, plain, (~v2_compts_1(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_526])).
% 4.67/1.85  tff(c_532, plain, (~v1_compts_1('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_529])).
% 4.67/1.85  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_532])).
% 4.67/1.85  tff(c_537, plain, (v2_compts_1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_526])).
% 4.67/1.85  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_83, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_76])).
% 4.67/1.85  tff(c_46, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_85, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_46])).
% 4.67/1.85  tff(c_100, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85])).
% 4.67/1.85  tff(c_36, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_95, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_38])).
% 4.67/1.85  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_101, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_44])).
% 4.67/1.85  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_279, plain, (![A_102, C_103, D_104, B_105]: (v2_compts_1(k7_relset_1(u1_struct_0(A_102), u1_struct_0(C_103), D_104, B_105), C_103) | ~v2_compts_1(B_105, A_102) | k2_relset_1(u1_struct_0(A_102), u1_struct_0(C_103), D_104)!=k2_struct_0(C_103) | ~v5_pre_topc(D_104, A_102, C_103) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(C_103)))) | ~v1_funct_2(D_104, u1_struct_0(A_102), u1_struct_0(C_103)) | ~v1_funct_1(D_104) | ~l1_pre_topc(C_103) | v2_struct_0(C_103) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.67/1.85  tff(c_293, plain, (![A_102, D_104, B_105]: (v2_compts_1(k7_relset_1(u1_struct_0(A_102), u1_struct_0('#skF_3'), D_104, B_105), '#skF_3') | ~v2_compts_1(B_105, A_102) | k2_relset_1(u1_struct_0(A_102), u1_struct_0('#skF_3'), D_104)!=k2_struct_0('#skF_3') | ~v5_pre_topc(D_104, A_102, '#skF_3') | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), k2_struct_0('#skF_3')))) | ~v1_funct_2(D_104, u1_struct_0(A_102), u1_struct_0('#skF_3')) | ~v1_funct_1(D_104) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_83, c_279])).
% 4.67/1.85  tff(c_306, plain, (![A_102, D_104, B_105]: (v2_compts_1(k7_relset_1(u1_struct_0(A_102), k2_struct_0('#skF_3'), D_104, B_105), '#skF_3') | ~v2_compts_1(B_105, A_102) | k2_relset_1(u1_struct_0(A_102), k2_struct_0('#skF_3'), D_104)!=k2_struct_0('#skF_3') | ~v5_pre_topc(D_104, A_102, '#skF_3') | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), k2_struct_0('#skF_3')))) | ~v1_funct_2(D_104, u1_struct_0(A_102), k2_struct_0('#skF_3')) | ~v1_funct_1(D_104) | v2_struct_0('#skF_3') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_83, c_83, c_293])).
% 4.67/1.85  tff(c_315, plain, (![A_109, D_110, B_111]: (v2_compts_1(k7_relset_1(u1_struct_0(A_109), k2_struct_0('#skF_3'), D_110, B_111), '#skF_3') | ~v2_compts_1(B_111, A_109) | k2_relset_1(u1_struct_0(A_109), k2_struct_0('#skF_3'), D_110)!=k2_struct_0('#skF_3') | ~v5_pre_topc(D_110, A_109, '#skF_3') | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), k2_struct_0('#skF_3')))) | ~v1_funct_2(D_110, u1_struct_0(A_109), k2_struct_0('#skF_3')) | ~v1_funct_1(D_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(negUnitSimplification, [status(thm)], [c_54, c_306])).
% 4.67/1.85  tff(c_323, plain, (![D_110, B_111]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'), D_110, B_111), '#skF_3') | ~v2_compts_1(B_111, '#skF_2') | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'), D_110)!=k2_struct_0('#skF_3') | ~v5_pre_topc(D_110, '#skF_2', '#skF_3') | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))) | ~v1_funct_2(D_110, u1_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1(D_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_315])).
% 4.67/1.85  tff(c_1084, plain, (![D_359, B_360]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), D_359, B_360), '#skF_3') | ~v2_compts_1(B_360, '#skF_2') | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), D_359)!=k2_struct_0('#skF_3') | ~v5_pre_topc(D_359, '#skF_2', '#skF_3') | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))) | ~v1_funct_2(D_359, k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1(D_359) | ~m1_subset_1(B_360, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_84, c_84, c_84, c_84, c_323])).
% 4.67/1.85  tff(c_1092, plain, (![B_360]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', B_360), '#skF_3') | ~v2_compts_1(B_360, '#skF_2') | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_360, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_101, c_1084])).
% 4.67/1.85  tff(c_1102, plain, (![B_361]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', B_361), '#skF_3') | ~v2_compts_1(B_361, '#skF_2') | ~m1_subset_1(B_361, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_100, c_36, c_95, c_1092])).
% 4.67/1.85  tff(c_14, plain, (![A_14, B_15, C_16, D_17]: (m1_subset_1(k7_relset_1(A_14, B_15, C_16, D_17), k1_zfmisc_1(B_15)) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.67/1.85  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_40, plain, (v8_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_138, plain, (![B_80, A_81]: (v4_pre_topc(B_80, A_81) | ~v2_compts_1(B_80, A_81) | ~v8_pre_topc(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/1.85  tff(c_148, plain, (![B_80]: (v4_pre_topc(B_80, '#skF_3') | ~v2_compts_1(B_80, '#skF_3') | ~v8_pre_topc('#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_138])).
% 4.67/1.85  tff(c_165, plain, (![B_85]: (v4_pre_topc(B_85, '#skF_3') | ~v2_compts_1(B_85, '#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_148])).
% 4.67/1.85  tff(c_263, plain, (![A_99, C_100, D_101]: (v4_pre_topc(k7_relset_1(A_99, k2_struct_0('#skF_3'), C_100, D_101), '#skF_3') | ~v2_compts_1(k7_relset_1(A_99, k2_struct_0('#skF_3'), C_100, D_101), '#skF_3') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, k2_struct_0('#skF_3')))))), inference(resolution, [status(thm)], [c_14, c_165])).
% 4.67/1.85  tff(c_309, plain, (![D_106]: (v4_pre_topc(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', D_106), '#skF_3') | ~v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', D_106), '#skF_3'))), inference(resolution, [status(thm)], [c_101, c_263])).
% 4.67/1.85  tff(c_30, plain, (~v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.67/1.85  tff(c_108, plain, (~v4_pre_topc(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_30])).
% 4.67/1.85  tff(c_313, plain, (~v2_compts_1(k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_309, c_108])).
% 4.67/1.85  tff(c_1105, plain, (~v2_compts_1('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1102, c_313])).
% 4.67/1.85  tff(c_1109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_537, c_1105])).
% 4.67/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.85  
% 4.67/1.85  Inference rules
% 4.67/1.85  ----------------------
% 4.67/1.85  #Ref     : 0
% 4.67/1.85  #Sup     : 213
% 4.67/1.85  #Fact    : 0
% 4.67/1.85  #Define  : 0
% 4.67/1.85  #Split   : 11
% 4.67/1.85  #Chain   : 0
% 4.67/1.85  #Close   : 0
% 4.67/1.85  
% 4.67/1.85  Ordering : KBO
% 4.67/1.85  
% 4.67/1.85  Simplification rules
% 4.67/1.85  ----------------------
% 4.67/1.85  #Subsume      : 44
% 4.67/1.85  #Demod        : 585
% 4.67/1.85  #Tautology    : 22
% 4.67/1.85  #SimpNegUnit  : 7
% 4.67/1.85  #BackRed      : 2
% 4.67/1.85  
% 4.67/1.85  #Partial instantiations: 0
% 4.67/1.85  #Strategies tried      : 1
% 4.67/1.85  
% 4.67/1.85  Timing (in seconds)
% 4.67/1.85  ----------------------
% 4.67/1.85  Preprocessing        : 0.35
% 4.67/1.85  Parsing              : 0.20
% 4.67/1.85  CNF conversion       : 0.03
% 4.67/1.85  Main loop            : 0.67
% 4.67/1.85  Inferencing          : 0.24
% 4.67/1.85  Reduction            : 0.23
% 4.67/1.85  Demodulation         : 0.17
% 4.67/1.85  BG Simplification    : 0.03
% 4.67/1.85  Subsumption          : 0.13
% 4.67/1.85  Abstraction          : 0.03
% 4.67/1.85  MUC search           : 0.00
% 4.67/1.85  Cooper               : 0.00
% 4.67/1.85  Total                : 1.07
% 4.67/1.85  Index Insertion      : 0.00
% 4.67/1.85  Index Deletion       : 0.00
% 4.67/1.85  Index Matching       : 0.00
% 4.67/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
