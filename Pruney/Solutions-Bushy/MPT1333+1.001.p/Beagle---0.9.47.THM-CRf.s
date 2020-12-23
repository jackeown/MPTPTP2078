%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1333+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 398 expanded)
%              Number of leaves         :   35 ( 156 expanded)
%              Depth                    :   16
%              Number of atoms          :  292 (1547 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v5_pre_topc(C,A,B)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => r1_tarski(k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)),k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_67,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_534,plain,(
    ! [A_176,B_177,C_178] :
      ( m1_subset_1('#skF_1'(A_176,B_177,C_178),k1_zfmisc_1(u1_struct_0(B_177)))
      | v5_pre_topc(C_178,A_176,B_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(B_177))))
      | ~ v1_funct_2(C_178,u1_struct_0(A_176),u1_struct_0(B_177))
      | ~ v1_funct_1(C_178)
      | ~ l1_pre_topc(B_177)
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_539,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_534])).

tff(c_543,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_539])).

tff(c_544,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_543])).

tff(c_97,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k8_relset_1(A_92,B_93,C_94,D_95) = k10_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_105,plain,(
    ! [D_96] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_96) = k10_relat_1('#skF_4',D_96) ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( m1_subset_1(k8_relset_1(A_30,B_31,C_32,D_33),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    ! [D_96] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_96),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_120,plain,(
    ! [D_97] : m1_subset_1(k10_relat_1('#skF_4',D_97),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_111])).

tff(c_28,plain,(
    ! [B_45,A_43] :
      ( r1_tarski(B_45,k2_pre_topc(A_43,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_125,plain,(
    ! [D_97] :
      ( r1_tarski(k10_relat_1('#skF_4',D_97),k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_97)))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_120,c_28])).

tff(c_131,plain,(
    ! [D_97] : r1_tarski(k10_relat_1('#skF_4',D_97),k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_97))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_125])).

tff(c_424,plain,(
    ! [A_147,B_148,C_149] :
      ( v4_pre_topc('#skF_1'(A_147,B_148,C_149),B_148)
      | v5_pre_topc(C_149,A_147,B_148)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),u1_struct_0(B_148))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_147),u1_struct_0(B_148))
      | ~ v1_funct_1(C_149)
      | ~ l1_pre_topc(B_148)
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_429,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_424])).

tff(c_433,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_429])).

tff(c_434,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_433])).

tff(c_34,plain,(
    ! [A_53,B_55] :
      ( k2_pre_topc(A_53,B_55) = B_55
      | ~ v4_pre_topc(B_55,A_53)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_556,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_1'('#skF_2','#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_544,c_34])).

tff(c_573,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_1'('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_434,c_556])).

tff(c_104,plain,(
    ! [D_95] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_95) = k10_relat_1('#skF_4',D_95) ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_60,plain,(
    ! [D_74] :
      ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | r1_tarski(k2_pre_topc('#skF_2',k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_74)),k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',D_74)))
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_212,plain,(
    ! [D_74] :
      ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | r1_tarski(k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_74)),k10_relat_1('#skF_4',k2_pre_topc('#skF_3',D_74)))
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_60])).

tff(c_214,plain,(
    ! [D_110] :
      ( r1_tarski(k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_110)),k10_relat_1('#skF_4',k2_pre_topc('#skF_3',D_110)))
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_212])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_217,plain,(
    ! [D_110] :
      ( k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_110)) = k10_relat_1('#skF_4',k2_pre_topc('#skF_3',D_110))
      | ~ r1_tarski(k10_relat_1('#skF_4',k2_pre_topc('#skF_3',D_110)),k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_110)))
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_214,c_4])).

tff(c_589,plain,
    ( k2_pre_topc('#skF_2',k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))) = k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')))
    | ~ r1_tarski(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),k2_pre_topc('#skF_2',k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_217])).

tff(c_620,plain,(
    k2_pre_topc('#skF_2',k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))) = k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_131,c_573,c_589])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_117,plain,(
    ! [D_96] : m1_subset_1(k10_relat_1('#skF_4',D_96),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_111])).

tff(c_145,plain,(
    ! [A_102,B_103] :
      ( k2_pre_topc(A_102,k2_pre_topc(A_102,B_103)) = k2_pre_topc(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_149,plain,(
    ! [D_96] :
      ( k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96))) = k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_117,c_145])).

tff(c_156,plain,(
    ! [D_96] : k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96))) = k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_149])).

tff(c_18,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_pre_topc(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [B_104,A_105] :
      ( v4_pre_topc(B_104,A_105)
      | k2_pre_topc(A_105,B_104) != B_104
      | ~ v2_pre_topc(A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_286,plain,(
    ! [A_128,B_129] :
      ( v4_pre_topc(k2_pre_topc(A_128,B_129),A_128)
      | k2_pre_topc(A_128,k2_pre_topc(A_128,B_129)) != k2_pre_topc(A_128,B_129)
      | ~ v2_pre_topc(A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_18,c_158])).

tff(c_290,plain,(
    ! [D_96] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96)),'#skF_2')
      | k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96))) != k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96))
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_117,c_286])).

tff(c_297,plain,(
    ! [D_96] : v4_pre_topc(k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_96)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_156,c_290])).

tff(c_669,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_297])).

tff(c_737,plain,(
    ! [A_181,B_182,C_183] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_181),u1_struct_0(B_182),C_183,'#skF_1'(A_181,B_182,C_183)),A_181)
      | v5_pre_topc(C_183,A_181,B_182)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_741,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_737])).

tff(c_743,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_36,c_669,c_741])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_743])).

tff(c_746,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_761,plain,(
    ! [B_189,A_190] :
      ( r1_tarski(B_189,k2_pre_topc(A_190,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_763,plain,
    ( r1_tarski('#skF_5',k2_pre_topc('#skF_3','#skF_5'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_761])).

tff(c_766,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_763])).

tff(c_26,plain,(
    ! [C_42,A_40,B_41] :
      ( r1_tarski(k10_relat_1(C_42,A_40),k10_relat_1(C_42,B_41))
      | ~ r1_tarski(A_40,B_41)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_771,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k8_relset_1(A_191,B_192,C_193,D_194) = k10_relat_1(C_193,D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_774,plain,(
    ! [D_194] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_194) = k10_relat_1('#skF_4',D_194) ),
    inference(resolution,[status(thm)],[c_36,c_771])).

tff(c_802,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( m1_subset_1(k8_relset_1(A_200,B_201,C_202,D_203),k1_zfmisc_1(A_200))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_819,plain,(
    ! [D_194] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_194),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_802])).

tff(c_825,plain,(
    ! [D_194] : m1_subset_1(k10_relat_1('#skF_4',D_194),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_819])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_826,plain,(
    ! [A_204,B_205] :
      ( k2_pre_topc(A_204,k2_pre_topc(A_204,B_205)) = k2_pre_topc(A_204,B_205)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_833,plain,
    ( k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_5')) = k2_pre_topc('#skF_3','#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_826])).

tff(c_838,plain,(
    k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_5')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_833])).

tff(c_885,plain,(
    ! [B_210,A_211] :
      ( v4_pre_topc(B_210,A_211)
      | k2_pre_topc(A_211,B_210) != B_210
      | ~ v2_pre_topc(A_211)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1031,plain,(
    ! [A_232,B_233] :
      ( v4_pre_topc(k2_pre_topc(A_232,B_233),A_232)
      | k2_pre_topc(A_232,k2_pre_topc(A_232,B_233)) != k2_pre_topc(A_232,B_233)
      | ~ v2_pre_topc(A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(resolution,[status(thm)],[c_18,c_885])).

tff(c_1040,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_3','#skF_5'),'#skF_3')
    | k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_5')) != k2_pre_topc('#skF_3','#skF_5')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1031])).

tff(c_1048,plain,(
    v4_pre_topc(k2_pre_topc('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_838,c_1040])).

tff(c_913,plain,(
    ! [A_213,B_214,C_215] :
      ( r1_tarski(k2_pre_topc(A_213,B_214),k2_pre_topc(A_213,C_215))
      | ~ r1_tarski(B_214,C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_924,plain,(
    ! [C_215] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),k2_pre_topc('#skF_3',C_215))
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_913])).

tff(c_934,plain,(
    ! [C_215] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),k2_pre_topc('#skF_3',C_215))
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_924])).

tff(c_1133,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_934])).

tff(c_1136,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1133])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_746,c_1136])).

tff(c_1142,plain,(
    m1_subset_1(k2_pre_topc('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_747,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1678,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_288),u1_struct_0(B_289),C_290,D_291),A_288)
      | ~ v4_pre_topc(D_291,B_289)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(u1_struct_0(B_289)))
      | ~ v5_pre_topc(C_290,A_288,B_289)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_288),u1_struct_0(B_289))))
      | ~ v1_funct_2(C_290,u1_struct_0(A_288),u1_struct_0(B_289))
      | ~ v1_funct_1(C_290)
      | ~ l1_pre_topc(B_289)
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1683,plain,(
    ! [D_291] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_291),'#skF_2')
      | ~ v4_pre_topc(D_291,'#skF_3')
      | ~ m1_subset_1(D_291,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_1678])).

tff(c_1688,plain,(
    ! [D_292] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_292),'#skF_2')
      | ~ v4_pre_topc(D_292,'#skF_3')
      | ~ m1_subset_1(D_292,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_747,c_774,c_1683])).

tff(c_1691,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')),'#skF_2')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1142,c_1688])).

tff(c_1705,plain,(
    v4_pre_topc(k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1691])).

tff(c_839,plain,(
    ! [D_206] : m1_subset_1(k10_relat_1('#skF_4',D_206),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_819])).

tff(c_844,plain,(
    ! [D_206] :
      ( k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_206)) = k10_relat_1('#skF_4',D_206)
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_206),'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_839,c_34])).

tff(c_852,plain,(
    ! [D_206] :
      ( k2_pre_topc('#skF_2',k10_relat_1('#skF_4',D_206)) = k10_relat_1('#skF_4',D_206)
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_206),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_844])).

tff(c_1714,plain,(
    k2_pre_topc('#skF_2',k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5'))) = k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1705,c_852])).

tff(c_30,plain,(
    ! [A_46,B_50,C_52] :
      ( r1_tarski(k2_pre_topc(A_46,B_50),k2_pre_topc(A_46,C_52))
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1739,plain,(
    ! [B_50] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_50),k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')))
      | ~ r1_tarski(B_50,k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')))
      | ~ m1_subset_1(k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_30])).

tff(c_1794,plain,(
    ! [B_297] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_297),k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')))
      | ~ r1_tarski(B_297,k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')))
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_825,c_1739])).

tff(c_50,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_2',k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_5')),k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3','#skF_5')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_749,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2',k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_5')),k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_50])).

tff(c_775,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2',k10_relat_1('#skF_4','#skF_5')),k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_749])).

tff(c_1811,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5')))
    | ~ m1_subset_1(k10_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1794,c_775])).

tff(c_1837,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4',k2_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_1811])).

tff(c_1845,plain,
    ( ~ r1_tarski('#skF_5',k2_pre_topc('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1837])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_766,c_1845])).

%------------------------------------------------------------------------------
