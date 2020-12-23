%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 229 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 ( 918 expanded)
%              Number of equality atoms :   15 (  95 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > u1_struct_0 > k3_funct_3 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( v5_pre_topc(C,A,B)
                        & v2_tops_2(D,B) )
                     => ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                         => ( E = k9_relat_1(k3_funct_3(C),D)
                           => v2_tops_2(E,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tops_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(k3_funct_3(B)))
       => k1_funct_1(k3_funct_3(B),A) = k10_relat_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_3)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
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

tff(c_54,plain,(
    ~ v2_tops_2('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_120,plain,(
    ! [A_134,B_135] :
      ( r2_hidden('#skF_6'(A_134,B_135),B_135)
      | v2_tops_2(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_134))))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,
    ( r2_hidden('#skF_6'('#skF_7','#skF_11'),'#skF_11')
    | v2_tops_2('#skF_11','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_120])).

tff(c_127,plain,
    ( r2_hidden('#skF_6'('#skF_7','#skF_11'),'#skF_11')
    | v2_tops_2('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_122])).

tff(c_128,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_127])).

tff(c_66,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_85,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    ! [A_78] :
      ( v1_funct_1(k3_funct_3(A_78))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_78] :
      ( v1_relat_1(k3_funct_3(A_78))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    k9_relat_1(k3_funct_3('#skF_9'),'#skF_10') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_152,plain,(
    ! [A_143,B_144,D_145] :
      ( r2_hidden('#skF_4'(A_143,B_144,k9_relat_1(A_143,B_144),D_145),B_144)
      | ~ r2_hidden(D_145,k9_relat_1(A_143,B_144))
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [D_145] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_145),'#skF_10')
      | ~ r2_hidden(D_145,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_167,plain,(
    ! [D_145] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_145),'#skF_10')
      | ~ r2_hidden(D_145,'#skF_11')
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_163])).

tff(c_168,plain,(
    ~ v1_relat_1(k3_funct_3('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_171,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_171])).

tff(c_176,plain,(
    ! [D_145] :
      ( ~ v1_funct_1(k3_funct_3('#skF_9'))
      | r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_145),'#skF_10')
      | ~ r2_hidden(D_145,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_182,plain,(
    ~ v1_funct_1(k3_funct_3('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_185,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_185])).

tff(c_190,plain,(
    ! [D_145] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_145),'#skF_10')
      | ~ r2_hidden(D_145,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_72,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_64,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_60,plain,(
    v2_tops_2('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_86,plain,(
    ! [A_119,C_120,B_121] :
      ( m1_subset_1(A_119,C_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(C_120))
      | ~ r2_hidden(A_119,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden(A_119,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_390,plain,(
    ! [C_175,A_176,B_177] :
      ( v4_pre_topc(C_175,A_176)
      | ~ r2_hidden(C_175,B_177)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ v2_tops_2(B_177,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_176))))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_836,plain,(
    ! [D_279,A_280] :
      ( v4_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),A_280)
      | ~ m1_subset_1('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ v2_tops_2('#skF_10',A_280)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_280))))
      | ~ l1_pre_topc(A_280)
      | ~ r2_hidden(D_279,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_190,c_390])).

tff(c_840,plain,(
    ! [D_279] :
      ( v4_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),'#skF_8')
      | ~ v2_tops_2('#skF_10','#skF_8')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8'))))
      | ~ l1_pre_topc('#skF_8')
      | ~ r2_hidden(D_279,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_95,c_836])).

tff(c_847,plain,(
    ! [D_279] :
      ( v4_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),'#skF_8')
      | ~ r2_hidden(D_279,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_279),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_60,c_840])).

tff(c_177,plain,(
    v1_relat_1(k3_funct_3('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_191,plain,(
    v1_funct_1(k3_funct_3('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_256,plain,(
    ! [A_154,B_155,D_156] :
      ( r2_hidden('#skF_4'(A_154,B_155,k9_relat_1(A_154,B_155),D_156),k1_relat_1(A_154))
      | ~ r2_hidden(D_156,k9_relat_1(A_154,B_155))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    ! [D_156] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_156),k1_relat_1(k3_funct_3('#skF_9')))
      | ~ r2_hidden(D_156,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_256])).

tff(c_273,plain,(
    ! [D_157] :
      ( r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_157),k1_relat_1(k3_funct_3('#skF_9')))
      | ~ r2_hidden(D_157,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_191,c_56,c_267])).

tff(c_50,plain,(
    ! [B_84,A_83] :
      ( k1_funct_1(k3_funct_3(B_84),A_83) = k10_relat_1(B_84,A_83)
      | ~ r2_hidden(A_83,k1_relat_1(k3_funct_3(B_84)))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_276,plain,(
    ! [D_157] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_157)) = k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_157))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_157,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_273,c_50])).

tff(c_331,plain,(
    ! [D_170] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_170)) = k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_170))
      | ~ r2_hidden(D_170,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_276])).

tff(c_207,plain,(
    ! [A_149,B_150,D_151] :
      ( k1_funct_1(A_149,'#skF_4'(A_149,B_150,k9_relat_1(A_149,B_150),D_151)) = D_151
      | ~ r2_hidden(D_151,k9_relat_1(A_149,B_150))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,(
    ! [D_151] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151)) = D_151
      | ~ r2_hidden(D_151,k9_relat_1(k3_funct_3('#skF_9'),'#skF_10'))
      | ~ v1_funct_1(k3_funct_3('#skF_9'))
      | ~ v1_relat_1(k3_funct_3('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_207])).

tff(c_223,plain,(
    ! [D_151] :
      ( k1_funct_1(k3_funct_3('#skF_9'),'#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_151)) = D_151
      | ~ r2_hidden(D_151,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_191,c_56,c_219])).

tff(c_340,plain,(
    ! [D_170] :
      ( k10_relat_1('#skF_9','#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_170)) = D_170
      | ~ r2_hidden(D_170,'#skF_11')
      | ~ r2_hidden(D_170,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_223])).

tff(c_68,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,(
    v5_pre_topc('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_107,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k8_relset_1(A_129,B_130,C_131,D_132) = k10_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_110,plain,(
    ! [D_132] : k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'),'#skF_9',D_132) = k10_relat_1('#skF_9',D_132) ),
    inference(resolution,[status(thm)],[c_66,c_107])).

tff(c_984,plain,(
    ! [A_296,B_297,C_298,D_299] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_296),u1_struct_0(B_297),C_298,D_299),A_296)
      | ~ v4_pre_topc(D_299,B_297)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(u1_struct_0(B_297)))
      | ~ v5_pre_topc(C_298,A_296,B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_296),u1_struct_0(B_297))))
      | ~ v1_funct_2(C_298,u1_struct_0(A_296),u1_struct_0(B_297))
      | ~ v1_funct_1(C_298)
      | ~ l1_pre_topc(B_297)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_986,plain,(
    ! [D_299] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'),'#skF_9',D_299),'#skF_7')
      | ~ v4_pre_topc(D_299,'#skF_8')
      | ~ m1_subset_1(D_299,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ v5_pre_topc('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_984])).

tff(c_990,plain,(
    ! [D_300] :
      ( v4_pre_topc(k10_relat_1('#skF_9',D_300),'#skF_7')
      | ~ v4_pre_topc(D_300,'#skF_8')
      | ~ m1_subset_1(D_300,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_62,c_110,c_986])).

tff(c_1002,plain,(
    ! [A_301] :
      ( v4_pre_topc(k10_relat_1('#skF_9',A_301),'#skF_7')
      | ~ v4_pre_topc(A_301,'#skF_8')
      | ~ r2_hidden(A_301,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_95,c_990])).

tff(c_1012,plain,(
    ! [D_303] :
      ( v4_pre_topc(D_303,'#skF_7')
      | ~ v4_pre_topc('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_303),'#skF_8')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_303),'#skF_10')
      | ~ r2_hidden(D_303,'#skF_11')
      | ~ r2_hidden(D_303,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_1002])).

tff(c_1017,plain,(
    ! [D_304] :
      ( v4_pre_topc(D_304,'#skF_7')
      | ~ r2_hidden(D_304,'#skF_11')
      | ~ r2_hidden('#skF_4'(k3_funct_3('#skF_9'),'#skF_10','#skF_11',D_304),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_847,c_1012])).

tff(c_1022,plain,(
    ! [D_305] :
      ( v4_pre_topc(D_305,'#skF_7')
      | ~ r2_hidden(D_305,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_190,c_1017])).

tff(c_38,plain,(
    ! [A_68,B_74] :
      ( ~ v4_pre_topc('#skF_6'(A_68,B_74),A_68)
      | v2_tops_2(B_74,A_68)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1029,plain,(
    ! [B_74] :
      ( v2_tops_2(B_74,'#skF_7')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))
      | ~ l1_pre_topc('#skF_7')
      | ~ r2_hidden('#skF_6'('#skF_7',B_74),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1022,c_38])).

tff(c_1036,plain,(
    ! [B_306] :
      ( v2_tops_2(B_306,'#skF_7')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))
      | ~ r2_hidden('#skF_6'('#skF_7',B_306),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1029])).

tff(c_1039,plain,
    ( v2_tops_2('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_11'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_58,c_1036])).

tff(c_1042,plain,(
    v2_tops_2('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1039])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1042])).

%------------------------------------------------------------------------------
