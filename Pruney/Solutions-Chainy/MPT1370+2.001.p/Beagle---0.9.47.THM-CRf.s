%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 436 expanded)
%              Number of leaves         :   36 ( 172 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 (1681 expanded)
%              Number of equality atoms :   18 ( 208 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
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

tff(f_110,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_70])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_42])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_84,c_8])).

tff(c_117,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_88])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_79,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_44])).

tff(c_101,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79])).

tff(c_34,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_122,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_36])).

tff(c_40,plain,(
    v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_20,plain,(
    ! [A_11] :
      ( v2_compts_1(k2_struct_0(A_11),A_11)
      | ~ v1_compts_1(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    v4_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_65,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_90,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_69])).

tff(c_214,plain,(
    ! [C_78,A_79,B_80] :
      ( v2_compts_1(C_78,A_79)
      | ~ v4_pre_topc(C_78,A_79)
      | ~ r1_tarski(C_78,B_80)
      | ~ v2_compts_1(B_80,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_237,plain,(
    ! [A_81] :
      ( v2_compts_1('#skF_4',A_81)
      | ~ v4_pre_topc('#skF_4',A_81)
      | ~ v2_compts_1(k2_struct_0('#skF_1'),A_81)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_90,c_214])).

tff(c_243,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_237])).

tff(c_249,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_91,c_78,c_30,c_243])).

tff(c_252,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_255,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_255])).

tff(c_260,plain,
    ( ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1')
    | v2_compts_1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_267,plain,(
    ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_296,plain,
    ( ~ v1_compts_1('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_267])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_296])).

tff(c_301,plain,(
    v2_compts_1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_347,plain,(
    ! [A_93,C_94,D_95,B_96] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_93),u1_struct_0(C_94),D_95,B_96),C_94)
      | ~ v2_compts_1(B_96,A_93)
      | k2_relset_1(u1_struct_0(A_93),u1_struct_0(C_94),D_95) != k2_struct_0(C_94)
      | ~ v5_pre_topc(D_95,A_93,C_94)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_93),u1_struct_0(C_94))))
      | ~ v1_funct_2(D_95,u1_struct_0(A_93),u1_struct_0(C_94))
      | ~ v1_funct_1(D_95)
      | ~ l1_pre_topc(C_94)
      | v2_struct_0(C_94)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_470,plain,(
    ! [A_122,C_123,A_124,B_125] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_122),u1_struct_0(C_123),A_124,B_125),C_123)
      | ~ v2_compts_1(B_125,A_122)
      | k2_relset_1(u1_struct_0(A_122),u1_struct_0(C_123),A_124) != k2_struct_0(C_123)
      | ~ v5_pre_topc(A_124,A_122,C_123)
      | ~ v1_funct_2(A_124,u1_struct_0(A_122),u1_struct_0(C_123))
      | ~ v1_funct_1(A_124)
      | ~ l1_pre_topc(C_123)
      | v2_struct_0(C_123)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ r1_tarski(A_124,k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(C_123))) ) ),
    inference(resolution,[status(thm)],[c_10,c_347])).

tff(c_482,plain,(
    ! [A_122,A_124,B_125] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_122),k2_struct_0('#skF_2'),A_124,B_125),'#skF_2')
      | ~ v2_compts_1(B_125,A_122)
      | k2_relset_1(u1_struct_0(A_122),u1_struct_0('#skF_2'),A_124) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_124,A_122,'#skF_2')
      | ~ v1_funct_2(A_124,u1_struct_0(A_122),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_124)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ r1_tarski(A_124,k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_470])).

tff(c_490,plain,(
    ! [A_122,A_124,B_125] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_122),k2_struct_0('#skF_2'),A_124,B_125),'#skF_2')
      | ~ v2_compts_1(B_125,A_122)
      | k2_relset_1(u1_struct_0(A_122),k2_struct_0('#skF_2'),A_124) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_124,A_122,'#skF_2')
      | ~ v1_funct_2(A_124,u1_struct_0(A_122),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_124)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ r1_tarski(A_124,k2_zfmisc_1(u1_struct_0(A_122),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_48,c_77,c_77,c_482])).

tff(c_512,plain,(
    ! [A_127,A_128,B_129] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_127),k2_struct_0('#skF_2'),A_128,B_129),'#skF_2')
      | ~ v2_compts_1(B_129,A_127)
      | k2_relset_1(u1_struct_0(A_127),k2_struct_0('#skF_2'),A_128) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_128,A_127,'#skF_2')
      | ~ v1_funct_2(A_128,u1_struct_0(A_127),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_128,k2_zfmisc_1(u1_struct_0(A_127),k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_490])).

tff(c_515,plain,(
    ! [A_128,B_129] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_128,B_129),'#skF_2')
      | ~ v2_compts_1(B_129,'#skF_1')
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_128) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_128,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_128,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_128,k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_512])).

tff(c_770,plain,(
    ! [A_201,B_202] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_201,B_202),'#skF_2')
      | ~ v2_compts_1(B_202,'#skF_1')
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_201) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_201,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_201,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_201)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_201,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_78,c_78,c_78,c_515])).

tff(c_89,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_84])).

tff(c_140,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( m1_subset_1(k7_relset_1(A_60,B_61,C_62,D_63),k1_zfmisc_1(B_61))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r1_tarski(k7_relset_1(A_64,B_65,C_66,D_67),B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_155,plain,(
    ! [D_67] : r1_tarski(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_67),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_89,c_145])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_166,plain,(
    ! [B_74,A_75] :
      ( v4_pre_topc(B_74,A_75)
      | ~ v2_compts_1(B_74,A_75)
      | ~ v8_pre_topc(A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,(
    ! [B_74] :
      ( v4_pre_topc(B_74,'#skF_2')
      | ~ v2_compts_1(B_74,'#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_166])).

tff(c_187,plain,(
    ! [B_76] :
      ( v4_pre_topc(B_76,'#skF_2')
      | ~ v2_compts_1(B_76,'#skF_2')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_180])).

tff(c_198,plain,(
    ! [A_77] :
      ( v4_pre_topc(A_77,'#skF_2')
      | ~ v2_compts_1(A_77,'#skF_2')
      | ~ r1_tarski(A_77,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_373,plain,(
    ! [D_97] :
      ( v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_97),'#skF_2')
      | ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_97),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_155,c_198])).

tff(c_28,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_138,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_28])).

tff(c_377,plain,(
    ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_373,c_138])).

tff(c_773,plain,
    ( ~ v2_compts_1('#skF_4','#skF_1')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_770,c_377])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_91,c_46,c_101,c_34,c_122,c_301,c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.46/1.54  
% 3.46/1.54  %Foreground sorts:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Background operators:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Foreground operators:
% 3.46/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.46/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.54  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.46/1.54  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.46/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.46/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.46/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.54  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.54  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.46/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.46/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.54  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 3.46/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.46/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.54  
% 3.46/1.56  tff(f_145, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_compts_1)).
% 3.46/1.56  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.46/1.56  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.46/1.56  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.56  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_compts_1)).
% 3.46/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.56  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.46/1.56  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_compts_1)).
% 3.46/1.56  tff(f_39, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.46/1.56  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.46/1.56  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.56  tff(c_60, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.56  tff(c_70, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_16, c_60])).
% 3.46/1.56  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_70])).
% 3.46/1.56  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_70])).
% 3.46/1.56  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_42])).
% 3.46/1.56  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.56  tff(c_88, plain, (r1_tarski('#skF_3', k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_84, c_8])).
% 3.46/1.56  tff(c_117, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_88])).
% 3.46/1.56  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_91, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32])).
% 3.46/1.56  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_79, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_44])).
% 3.46/1.56  tff(c_101, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79])).
% 3.46/1.56  tff(c_34, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_122, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_36])).
% 3.46/1.56  tff(c_40, plain, (v1_compts_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_20, plain, (![A_11]: (v2_compts_1(k2_struct_0(A_11), A_11) | ~v1_compts_1(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.56  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.56  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_30, plain, (v4_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_65, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.56  tff(c_69, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_65])).
% 3.46/1.56  tff(c_90, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_69])).
% 3.46/1.56  tff(c_214, plain, (![C_78, A_79, B_80]: (v2_compts_1(C_78, A_79) | ~v4_pre_topc(C_78, A_79) | ~r1_tarski(C_78, B_80) | ~v2_compts_1(B_80, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.56  tff(c_237, plain, (![A_81]: (v2_compts_1('#skF_4', A_81) | ~v4_pre_topc('#skF_4', A_81) | ~v2_compts_1(k2_struct_0('#skF_1'), A_81) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(resolution, [status(thm)], [c_90, c_214])).
% 3.46/1.56  tff(c_243, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v4_pre_topc('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_237])).
% 3.46/1.56  tff(c_249, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_91, c_78, c_30, c_243])).
% 3.46/1.56  tff(c_252, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_249])).
% 3.46/1.56  tff(c_255, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_252])).
% 3.46/1.56  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_255])).
% 3.46/1.56  tff(c_260, plain, (~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1') | v2_compts_1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_249])).
% 3.46/1.56  tff(c_267, plain, (~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_260])).
% 3.46/1.56  tff(c_296, plain, (~v1_compts_1('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_267])).
% 3.46/1.56  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_296])).
% 3.46/1.56  tff(c_301, plain, (v2_compts_1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_260])).
% 3.46/1.56  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_347, plain, (![A_93, C_94, D_95, B_96]: (v2_compts_1(k7_relset_1(u1_struct_0(A_93), u1_struct_0(C_94), D_95, B_96), C_94) | ~v2_compts_1(B_96, A_93) | k2_relset_1(u1_struct_0(A_93), u1_struct_0(C_94), D_95)!=k2_struct_0(C_94) | ~v5_pre_topc(D_95, A_93, C_94) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_93), u1_struct_0(C_94)))) | ~v1_funct_2(D_95, u1_struct_0(A_93), u1_struct_0(C_94)) | ~v1_funct_1(D_95) | ~l1_pre_topc(C_94) | v2_struct_0(C_94) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.46/1.56  tff(c_470, plain, (![A_122, C_123, A_124, B_125]: (v2_compts_1(k7_relset_1(u1_struct_0(A_122), u1_struct_0(C_123), A_124, B_125), C_123) | ~v2_compts_1(B_125, A_122) | k2_relset_1(u1_struct_0(A_122), u1_struct_0(C_123), A_124)!=k2_struct_0(C_123) | ~v5_pre_topc(A_124, A_122, C_123) | ~v1_funct_2(A_124, u1_struct_0(A_122), u1_struct_0(C_123)) | ~v1_funct_1(A_124) | ~l1_pre_topc(C_123) | v2_struct_0(C_123) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~r1_tarski(A_124, k2_zfmisc_1(u1_struct_0(A_122), u1_struct_0(C_123))))), inference(resolution, [status(thm)], [c_10, c_347])).
% 3.46/1.56  tff(c_482, plain, (![A_122, A_124, B_125]: (v2_compts_1(k7_relset_1(u1_struct_0(A_122), k2_struct_0('#skF_2'), A_124, B_125), '#skF_2') | ~v2_compts_1(B_125, A_122) | k2_relset_1(u1_struct_0(A_122), u1_struct_0('#skF_2'), A_124)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_124, A_122, '#skF_2') | ~v1_funct_2(A_124, u1_struct_0(A_122), u1_struct_0('#skF_2')) | ~v1_funct_1(A_124) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~r1_tarski(A_124, k2_zfmisc_1(u1_struct_0(A_122), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_77, c_470])).
% 3.46/1.56  tff(c_490, plain, (![A_122, A_124, B_125]: (v2_compts_1(k7_relset_1(u1_struct_0(A_122), k2_struct_0('#skF_2'), A_124, B_125), '#skF_2') | ~v2_compts_1(B_125, A_122) | k2_relset_1(u1_struct_0(A_122), k2_struct_0('#skF_2'), A_124)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_124, A_122, '#skF_2') | ~v1_funct_2(A_124, u1_struct_0(A_122), k2_struct_0('#skF_2')) | ~v1_funct_1(A_124) | v2_struct_0('#skF_2') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~r1_tarski(A_124, k2_zfmisc_1(u1_struct_0(A_122), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_48, c_77, c_77, c_482])).
% 3.46/1.56  tff(c_512, plain, (![A_127, A_128, B_129]: (v2_compts_1(k7_relset_1(u1_struct_0(A_127), k2_struct_0('#skF_2'), A_128, B_129), '#skF_2') | ~v2_compts_1(B_129, A_127) | k2_relset_1(u1_struct_0(A_127), k2_struct_0('#skF_2'), A_128)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_128, A_127, '#skF_2') | ~v1_funct_2(A_128, u1_struct_0(A_127), k2_struct_0('#skF_2')) | ~v1_funct_1(A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~r1_tarski(A_128, k2_zfmisc_1(u1_struct_0(A_127), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_490])).
% 3.46/1.56  tff(c_515, plain, (![A_128, B_129]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_128, B_129), '#skF_2') | ~v2_compts_1(B_129, '#skF_1') | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_128)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_128, '#skF_1', '#skF_2') | ~v1_funct_2(A_128, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_128, k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_512])).
% 3.46/1.56  tff(c_770, plain, (![A_201, B_202]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_201, B_202), '#skF_2') | ~v2_compts_1(B_202, '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_201)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_201, '#skF_1', '#skF_2') | ~v1_funct_2(A_201, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_201) | ~m1_subset_1(B_202, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_201, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_78, c_78, c_78, c_515])).
% 3.46/1.56  tff(c_89, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_84])).
% 3.46/1.56  tff(c_140, plain, (![A_60, B_61, C_62, D_63]: (m1_subset_1(k7_relset_1(A_60, B_61, C_62, D_63), k1_zfmisc_1(B_61)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.56  tff(c_145, plain, (![A_64, B_65, C_66, D_67]: (r1_tarski(k7_relset_1(A_64, B_65, C_66, D_67), B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(resolution, [status(thm)], [c_140, c_8])).
% 3.46/1.56  tff(c_155, plain, (![D_67]: (r1_tarski(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_67), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_89, c_145])).
% 3.46/1.56  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_38, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_166, plain, (![B_74, A_75]: (v4_pre_topc(B_74, A_75) | ~v2_compts_1(B_74, A_75) | ~v8_pre_topc(A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.56  tff(c_180, plain, (![B_74]: (v4_pre_topc(B_74, '#skF_2') | ~v2_compts_1(B_74, '#skF_2') | ~v8_pre_topc('#skF_2') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_166])).
% 3.46/1.56  tff(c_187, plain, (![B_76]: (v4_pre_topc(B_76, '#skF_2') | ~v2_compts_1(B_76, '#skF_2') | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_180])).
% 3.46/1.56  tff(c_198, plain, (![A_77]: (v4_pre_topc(A_77, '#skF_2') | ~v2_compts_1(A_77, '#skF_2') | ~r1_tarski(A_77, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_187])).
% 3.46/1.56  tff(c_373, plain, (![D_97]: (v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_97), '#skF_2') | ~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_97), '#skF_2'))), inference(resolution, [status(thm)], [c_155, c_198])).
% 3.46/1.56  tff(c_28, plain, (~v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.46/1.56  tff(c_138, plain, (~v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_28])).
% 3.46/1.56  tff(c_377, plain, (~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_373, c_138])).
% 3.46/1.56  tff(c_773, plain, (~v2_compts_1('#skF_4', '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_770, c_377])).
% 3.46/1.56  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_91, c_46, c_101, c_34, c_122, c_301, c_773])).
% 3.46/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.56  
% 3.46/1.56  Inference rules
% 3.46/1.56  ----------------------
% 3.46/1.56  #Ref     : 0
% 3.46/1.56  #Sup     : 143
% 3.46/1.56  #Fact    : 0
% 3.46/1.56  #Define  : 0
% 3.46/1.56  #Split   : 10
% 3.46/1.56  #Chain   : 0
% 3.46/1.56  #Close   : 0
% 3.46/1.56  
% 3.46/1.56  Ordering : KBO
% 3.46/1.56  
% 3.46/1.56  Simplification rules
% 3.46/1.56  ----------------------
% 3.46/1.56  #Subsume      : 36
% 3.46/1.56  #Demod        : 361
% 3.46/1.56  #Tautology    : 18
% 3.46/1.56  #SimpNegUnit  : 5
% 3.46/1.56  #BackRed      : 4
% 3.46/1.56  
% 3.46/1.56  #Partial instantiations: 0
% 3.46/1.56  #Strategies tried      : 1
% 3.46/1.56  
% 3.46/1.56  Timing (in seconds)
% 3.46/1.56  ----------------------
% 3.46/1.57  Preprocessing        : 0.34
% 3.46/1.57  Parsing              : 0.18
% 3.46/1.57  CNF conversion       : 0.03
% 3.46/1.57  Main loop            : 0.45
% 3.46/1.57  Inferencing          : 0.16
% 3.46/1.57  Reduction            : 0.17
% 3.46/1.57  Demodulation         : 0.12
% 3.46/1.57  BG Simplification    : 0.02
% 3.46/1.57  Subsumption          : 0.09
% 3.46/1.57  Abstraction          : 0.02
% 3.46/1.57  MUC search           : 0.00
% 3.46/1.57  Cooper               : 0.00
% 3.46/1.57  Total                : 0.83
% 3.46/1.57  Index Insertion      : 0.00
% 3.46/1.57  Index Deletion       : 0.00
% 3.46/1.57  Index Matching       : 0.00
% 3.46/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
