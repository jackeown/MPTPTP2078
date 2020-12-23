%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 272 expanded)
%              Number of leaves         :   49 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 (1147 expanded)
%              Number of equality atoms :   21 ( 118 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > u1_struct_0 > k3_funct_3 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k3_funct_3,type,(
    k3_funct_3: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( v5_pre_topc(C,A,B)
                        & v1_tops_2(D,B) )
                     => ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                         => ( E = k9_relat_1(k3_funct_3(C),D)
                           => v1_tops_2(E,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k3_funct_3(A))
        & v1_funct_1(k3_funct_3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(k3_funct_3(B)))
       => k1_funct_1(k3_funct_3(B),A) = k10_relat_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_3)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => ( v5_pre_topc(C,A,B)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( v3_pre_topc(D,B)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_68,plain,(
    ~ v1_tops_2('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_90,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_72,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_139,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_5'(A_140,B_141),B_141)
      | v1_tops_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_140))))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_11'),'#skF_11')
    | v1_tops_2('#skF_11','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_139])).

tff(c_146,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_11'),'#skF_11')
    | v1_tops_2('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_141])).

tff(c_147,plain,(
    r2_hidden('#skF_5'('#skF_7','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_146])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_99,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_103,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_99])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    ! [A_56] :
      ( v1_funct_1(k3_funct_3(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_56] :
      ( v1_relat_1(k3_funct_3(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    k9_relat_1(k3_funct_3('#skF_9'),'#skF_10') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_174,plain,(
    ! [A_149,B_150,D_151] :
      ( r2_hidden('#skF_4'(A_149,B_150,k9_relat_1(A_149,B_150),D_151),B_150)
      | ~ r2_hidden(D_151,k9_relat_1(A_149,B_150))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [D_151] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151),'#skF_10')
      | ~ r2_hidden(D_151,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_174])).

tff(c_189,plain,(
    ! [D_151] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151),'#skF_10')
      | ~ r2_hidden(D_151,'#skF_11')
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_185])).

tff(c_190,plain,(
    ~ v1_relat_1(k3_funct_3('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_194,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_190])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_84,c_194])).

tff(c_199,plain,(
    ! [D_151] :
      ( ~ v1_funct_1(k3_funct_3('#skF_9'))
      | r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151),'#skF_10')
      | ~ r2_hidden(D_151,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_201,plain,(
    ~ v1_funct_1(k3_funct_3('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_204,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_84,c_204])).

tff(c_209,plain,(
    ! [D_151] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151),'#skF_10')
      | ~ r2_hidden(D_151,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_86,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_74,plain,(
    v1_tops_2('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_104,plain,(
    ! [A_123,C_124,B_125] :
      ( m1_subset_1(A_123,C_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(C_124))
      | ~ r2_hidden(A_123,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_113,plain,(
    ! [A_123] :
      ( m1_subset_1(A_123,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden(A_123,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_78,c_104])).

tff(c_403,plain,(
    ! [C_179,A_180,B_181] :
      ( v3_pre_topc(C_179,A_180)
      | ~ r2_hidden(C_179,B_181)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ v1_tops_2(B_181,A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_180))))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_843,plain,(
    ! [D_280,A_281] :
      ( v3_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),A_281)
      | ~ m1_subset_1('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ v1_tops_2('#skF_10',A_281)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_281))))
      | ~ l1_pre_topc(A_281)
      | ~ r2_hidden(D_280,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_209,c_403])).

tff(c_847,plain,(
    ! [D_280] :
      ( v3_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),'#skF_8')
      | ~ v1_tops_2('#skF_10','#skF_8')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8'))))
      | ~ l1_pre_topc('#skF_8')
      | ~ r2_hidden(D_280,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_113,c_843])).

tff(c_854,plain,(
    ! [D_280] :
      ( v3_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),'#skF_8')
      | ~ r2_hidden(D_280,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_280),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_78,c_74,c_847])).

tff(c_200,plain,(
    v1_relat_1(k3_funct_3('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_210,plain,(
    v1_funct_1(k3_funct_3('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_211,plain,(
    ! [A_152,B_153,D_154] :
      ( r2_hidden('#skF_4'(A_152,B_153,k9_relat_1(A_152,B_153),D_154),k1_relat_1(A_152))
      | ~ r2_hidden(D_154,k9_relat_1(A_152,B_153))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_222,plain,(
    ! [D_154] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_154),k1_relat_1(k3_funct_3('#skF_9')))
      | ~ r2_hidden(D_154,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_211])).

tff(c_235,plain,(
    ! [D_156] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_156),k1_relat_1(k3_funct_3('#skF_9')))
      | ~ r2_hidden(D_156,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_210,c_70,c_222])).

tff(c_48,plain,(
    ! [B_64,A_63] :
      ( k1_funct_1(k3_funct_3(B_64),A_63) = k10_relat_1(B_64,A_63)
      | ~ r2_hidden(A_63,k1_relat_1(k3_funct_3(B_64)))
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_238,plain,(
    ! [D_156] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_156)) = k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_156))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_156,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_235,c_48])).

tff(c_344,plain,(
    ! [D_174] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_174)) = k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_174))
      | ~ r2_hidden(D_174,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_84,c_238])).

tff(c_260,plain,(
    ! [A_158,B_159,D_160] :
      ( k1_funct_1(A_158,'#skF_4'(A_158,B_159,k9_relat_1(A_158,B_159),D_160)) = D_160
      | ~ r2_hidden(D_160,k9_relat_1(A_158,B_159))
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_276,plain,(
    ! [D_160] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_160)) = D_160
      | ~ r2_hidden(D_160,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_260])).

tff(c_282,plain,(
    ! [D_160] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_160)) = D_160
      | ~ r2_hidden(D_160,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_210,c_70,c_276])).

tff(c_350,plain,(
    ! [D_174] :
      ( k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_174)) = D_174
      | ~ r2_hidden(D_174,'#skF_11')
      | ~ r2_hidden(D_174,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_282])).

tff(c_40,plain,(
    ! [A_57] :
      ( l1_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_82,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    v5_pre_topc('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_125,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k8_relset_1(A_133,B_134,C_135,D_136) = k10_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_128,plain,(
    ! [D_136] : k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'),'#skF_9',D_136) = k10_relat_1('#skF_9',D_136) ),
    inference(resolution,[status(thm)],[c_80,c_125])).

tff(c_1514,plain,(
    ! [B_363,A_364,C_365,D_366] :
      ( k2_struct_0(B_363) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_364),u1_struct_0(B_363),C_365,D_366),A_364)
      | ~ v3_pre_topc(D_366,B_363)
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0(B_363)))
      | ~ v5_pre_topc(C_365,A_364,B_363)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_364),u1_struct_0(B_363))))
      | ~ v1_funct_2(C_365,u1_struct_0(A_364),u1_struct_0(B_363))
      | ~ v1_funct_1(C_365)
      | ~ l1_pre_topc(B_363)
      | ~ l1_pre_topc(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1516,plain,(
    ! [D_366] :
      ( k2_struct_0('#skF_8') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'),'#skF_9',D_366),'#skF_7')
      | ~ v3_pre_topc(D_366,'#skF_8')
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ v5_pre_topc('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_1514])).

tff(c_1519,plain,(
    ! [D_366] :
      ( k2_struct_0('#skF_8') = k1_xboole_0
      | v3_pre_topc(k10_relat_1('#skF_9',D_366),'#skF_7')
      | ~ v3_pre_topc(D_366,'#skF_8')
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_82,c_76,c_128,c_1516])).

tff(c_1520,plain,(
    k2_struct_0('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_44,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k2_struct_0(A_58))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1524,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_44])).

tff(c_1528,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1524])).

tff(c_1529,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1528])).

tff(c_1533,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_1529])).

tff(c_1537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1533])).

tff(c_1540,plain,(
    ! [D_367] :
      ( v3_pre_topc(k10_relat_1('#skF_9',D_367),'#skF_7')
      | ~ v3_pre_topc(D_367,'#skF_8')
      | ~ m1_subset_1(D_367,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_1552,plain,(
    ! [A_368] :
      ( v3_pre_topc(k10_relat_1('#skF_9',A_368),'#skF_7')
      | ~ v3_pre_topc(A_368,'#skF_8')
      | ~ r2_hidden(A_368,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_113,c_1540])).

tff(c_1682,plain,(
    ! [D_379] :
      ( v3_pre_topc(D_379,'#skF_7')
      | ~ v3_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_379),'#skF_8')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_379),'#skF_10')
      | ~ r2_hidden(D_379,'#skF_11')
      | ~ r2_hidden(D_379,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1552])).

tff(c_1687,plain,(
    ! [D_380] :
      ( v3_pre_topc(D_380,'#skF_7')
      | ~ r2_hidden(D_380,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_380),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_854,c_1682])).

tff(c_1693,plain,(
    ! [D_383] :
      ( v3_pre_topc(D_383,'#skF_7')
      | ~ r2_hidden(D_383,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_209,c_1687])).

tff(c_30,plain,(
    ! [A_46,B_52] :
      ( ~ v3_pre_topc('#skF_5'(A_46,B_52),A_46)
      | v1_tops_2(B_52,A_46)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_46))))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1704,plain,(
    ! [B_52] :
      ( v1_tops_2(B_52,'#skF_7')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))
      | ~ l1_pre_topc('#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_7',B_52),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1693,c_30])).

tff(c_1714,plain,(
    ! [B_384] :
      ( v1_tops_2(B_384,'#skF_7')
      | ~ m1_subset_1(B_384,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))
      | ~ r2_hidden('#skF_5'('#skF_7',B_384),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1704])).

tff(c_1717,plain,
    ( v1_tops_2('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7','#skF_11'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_1714])).

tff(c_1720,plain,(
    v1_tops_2('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1717])).

tff(c_1722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1720])).

%------------------------------------------------------------------------------
