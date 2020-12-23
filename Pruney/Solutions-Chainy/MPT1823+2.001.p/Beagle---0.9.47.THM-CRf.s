%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:09 EST 2020

% Result     : Theorem 8.79s
% Output     : CNFRefutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :  242 (7038 expanded)
%              Number of leaves         :   40 (2777 expanded)
%              Depth                    :   31
%              Number of atoms          :  936 (53452 expanded)
%              Number of equality atoms :   30 (3349 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_298,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( A = k1_tsep_1(A,C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                         => r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k2_tmap_1(A,B,E,C),k2_tmap_1(A,B,E,D))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_223,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_183,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_205,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_259,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

tff(f_41,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_133,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( v1_funct_1(k2_tmap_1(A_151,B_152,C_153,D_154))
      | ~ l1_struct_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151),u1_struct_0(B_152))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_151),u1_struct_0(B_152))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0(B_152)
      | ~ l1_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_135,plain,(
    ! [D_154] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ l1_struct_0(D_154)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_138,plain,(
    ! [D_154] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ l1_struct_0(D_154)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_135])).

tff(c_139,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_142,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_142])).

tff(c_147,plain,(
    ! [D_154] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ l1_struct_0(D_154) ) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_149,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_152,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_152])).

tff(c_158,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_174,plain,(
    ! [C_169,A_166,F_168,D_167,B_165] :
      ( r1_funct_2(A_166,B_165,C_169,D_167,F_168,F_168)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_169,D_167)))
      | ~ v1_funct_2(F_168,C_169,D_167)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165)))
      | ~ v1_funct_2(F_168,A_166,B_165)
      | ~ v1_funct_1(F_168)
      | v1_xboole_0(D_167)
      | v1_xboole_0(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_176,plain,(
    ! [A_166,B_165] :
      ( r1_funct_2(A_166,B_165,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_166,B_165)))
      | ~ v1_funct_2('#skF_5',A_166,B_165)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_165) ) ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_179,plain,(
    ! [A_166,B_165] :
      ( r1_funct_2(A_166,B_165,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_166,B_165)))
      | ~ v1_funct_2('#skF_5',A_166,B_165)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_176])).

tff(c_180,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_183,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_10])).

tff(c_186,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_183])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_186])).

tff(c_190,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_189,plain,(
    ! [A_166,B_165] :
      ( r1_funct_2(A_166,B_165,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_166,B_165)))
      | ~ v1_funct_2('#skF_5',A_166,B_165)
      | v1_xboole_0(B_165) ) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_75,plain,(
    ! [B_133,A_134] :
      ( l1_pre_topc(B_133)
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_148,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_32,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( m1_subset_1(k2_tmap_1(A_71,B_72,C_73,D_74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_74),u1_struct_0(B_72))))
      | ~ l1_struct_0(D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0(B_72))
      | ~ v1_funct_1(C_73)
      | ~ l1_struct_0(B_72)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_167,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( v1_funct_2(k2_tmap_1(A_160,B_161,C_162,D_163),u1_struct_0(D_163),u1_struct_0(B_161))
      | ~ l1_struct_0(D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160),u1_struct_0(B_161))))
      | ~ v1_funct_2(C_162,u1_struct_0(A_160),u1_struct_0(B_161))
      | ~ v1_funct_1(C_162)
      | ~ l1_struct_0(B_161)
      | ~ l1_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_169,plain,(
    ! [D_163] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_163)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_172,plain,(
    ! [D_163] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_169])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_81])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_48,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_389,plain,(
    ! [A_209,B_210,D_212,E_207,F_211,C_208] :
      ( v1_funct_2(k10_tmap_1(A_209,B_210,C_208,D_212,E_207,F_211),u1_struct_0(k1_tsep_1(A_209,C_208,D_212)),u1_struct_0(B_210))
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_212),u1_struct_0(B_210))))
      | ~ v1_funct_2(F_211,u1_struct_0(D_212),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_208),u1_struct_0(B_210))))
      | ~ v1_funct_2(E_207,u1_struct_0(C_208),u1_struct_0(B_210))
      | ~ v1_funct_1(E_207)
      | ~ m1_pre_topc(D_212,A_209)
      | v2_struct_0(D_212)
      | ~ m1_pre_topc(C_208,A_209)
      | v2_struct_0(C_208)
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_392,plain,(
    ! [B_210,E_207,F_211] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_207,F_211),u1_struct_0('#skF_1'),u1_struct_0(B_210))
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_210))))
      | ~ v1_funct_2(F_211,u1_struct_0('#skF_4'),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_210))))
      | ~ v1_funct_2(E_207,u1_struct_0('#skF_3'),u1_struct_0(B_210))
      | ~ v1_funct_1(E_207)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_389])).

tff(c_394,plain,(
    ! [B_210,E_207,F_211] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_207,F_211),u1_struct_0('#skF_1'),u1_struct_0(B_210))
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_210))))
      | ~ v1_funct_2(F_211,u1_struct_0('#skF_4'),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_210))))
      | ~ v1_funct_2(E_207,u1_struct_0('#skF_3'),u1_struct_0(B_210))
      | ~ v1_funct_1(E_207)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_50,c_392])).

tff(c_439,plain,(
    ! [B_220,E_221,F_222] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_220,'#skF_3','#skF_4',E_221,F_222),u1_struct_0('#skF_1'),u1_struct_0(B_220))
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_220))))
      | ~ v1_funct_2(F_222,u1_struct_0('#skF_4'),u1_struct_0(B_220))
      | ~ v1_funct_1(F_222)
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_220))))
      | ~ v1_funct_2(E_221,u1_struct_0('#skF_3'),u1_struct_0(B_220))
      | ~ v1_funct_1(E_221)
      | ~ l1_pre_topc(B_220)
      | ~ v2_pre_topc(B_220)
      | v2_struct_0(B_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_52,c_394])).

tff(c_443,plain,(
    ! [B_72,E_221,A_71,C_73] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_72,'#skF_3','#skF_4',E_221,k2_tmap_1(A_71,B_72,C_73,'#skF_4')),u1_struct_0('#skF_1'),u1_struct_0(B_72))
      | ~ v1_funct_2(k2_tmap_1(A_71,B_72,C_73,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_72))
      | ~ v1_funct_1(k2_tmap_1(A_71,B_72,C_73,'#skF_4'))
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_72))))
      | ~ v1_funct_2(E_221,u1_struct_0('#skF_3'),u1_struct_0(B_72))
      | ~ v1_funct_1(E_221)
      | ~ l1_pre_topc(B_72)
      | ~ v2_pre_topc(B_72)
      | v2_struct_0(B_72)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0(B_72))
      | ~ v1_funct_1(C_73)
      | ~ l1_struct_0(B_72)
      | ~ l1_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_32,c_439])).

tff(c_1215,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_1218,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1215])).

tff(c_1222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1218])).

tff(c_1224,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_157,plain,(
    ! [D_154] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ l1_struct_0(D_154) ) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_1225,plain,(
    ! [B_402,E_403,A_404,C_405] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_402,'#skF_3','#skF_4',E_403,k2_tmap_1(A_404,B_402,C_405,'#skF_4')),u1_struct_0('#skF_1'),u1_struct_0(B_402))
      | ~ v1_funct_2(k2_tmap_1(A_404,B_402,C_405,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_402))
      | ~ v1_funct_1(k2_tmap_1(A_404,B_402,C_405,'#skF_4'))
      | ~ m1_subset_1(E_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_402))))
      | ~ v1_funct_2(E_403,u1_struct_0('#skF_3'),u1_struct_0(B_402))
      | ~ v1_funct_1(E_403)
      | ~ l1_pre_topc(B_402)
      | ~ v2_pre_topc(B_402)
      | v2_struct_0(B_402)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),u1_struct_0(B_402))))
      | ~ v1_funct_2(C_405,u1_struct_0(A_404),u1_struct_0(B_402))
      | ~ v1_funct_1(C_405)
      | ~ l1_struct_0(B_402)
      | ~ l1_struct_0(A_404) ) ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_492,plain,(
    ! [B_237,D_239,E_234,C_235,F_238,A_236] :
      ( m1_subset_1(k10_tmap_1(A_236,B_237,C_235,D_239,E_234,F_238),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_236,C_235,D_239)),u1_struct_0(B_237))))
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_239),u1_struct_0(B_237))))
      | ~ v1_funct_2(F_238,u1_struct_0(D_239),u1_struct_0(B_237))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_235),u1_struct_0(B_237))))
      | ~ v1_funct_2(E_234,u1_struct_0(C_235),u1_struct_0(B_237))
      | ~ v1_funct_1(E_234)
      | ~ m1_pre_topc(D_239,A_236)
      | v2_struct_0(D_239)
      | ~ m1_pre_topc(C_235,A_236)
      | v2_struct_0(C_235)
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_512,plain,(
    ! [B_237,E_234,F_238] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_237,'#skF_3','#skF_4',E_234,F_238),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_237))))
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_237))))
      | ~ v1_funct_2(F_238,u1_struct_0('#skF_4'),u1_struct_0(B_237))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_237))))
      | ~ v1_funct_2(E_234,u1_struct_0('#skF_3'),u1_struct_0(B_237))
      | ~ v1_funct_1(E_234)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_492])).

tff(c_525,plain,(
    ! [B_237,E_234,F_238] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_237,'#skF_3','#skF_4',E_234,F_238),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_237))))
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_237))))
      | ~ v1_funct_2(F_238,u1_struct_0('#skF_4'),u1_struct_0(B_237))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_237))))
      | ~ v1_funct_2(E_234,u1_struct_0('#skF_3'),u1_struct_0(B_237))
      | ~ v1_funct_1(E_234)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_50,c_512])).

tff(c_526,plain,(
    ! [B_237,E_234,F_238] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_237,'#skF_3','#skF_4',E_234,F_238),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_237))))
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_237))))
      | ~ v1_funct_2(F_238,u1_struct_0('#skF_4'),u1_struct_0(B_237))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_237))))
      | ~ v1_funct_2(E_234,u1_struct_0('#skF_3'),u1_struct_0(B_237))
      | ~ v1_funct_1(E_234)
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_52,c_525])).

tff(c_656,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_659,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_656])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_659])).

tff(c_665,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_291,plain,(
    ! [B_204,E_201,A_203,C_202,F_205,D_206] :
      ( v1_funct_1(k10_tmap_1(A_203,B_204,C_202,D_206,E_201,F_205))
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0(B_204))))
      | ~ v1_funct_2(F_205,u1_struct_0(D_206),u1_struct_0(B_204))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202),u1_struct_0(B_204))))
      | ~ v1_funct_2(E_201,u1_struct_0(C_202),u1_struct_0(B_204))
      | ~ v1_funct_1(E_201)
      | ~ m1_pre_topc(D_206,A_203)
      | v2_struct_0(D_206)
      | ~ m1_pre_topc(C_202,A_203)
      | v2_struct_0(C_202)
      | ~ l1_pre_topc(B_204)
      | ~ v2_pre_topc(B_204)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_779,plain,(
    ! [C_326,C_322,A_320,D_325,B_324,E_321,A_323] :
      ( v1_funct_1(k10_tmap_1(A_320,B_324,C_322,D_325,E_321,k2_tmap_1(A_323,B_324,C_326,D_325)))
      | ~ v1_funct_2(k2_tmap_1(A_323,B_324,C_326,D_325),u1_struct_0(D_325),u1_struct_0(B_324))
      | ~ v1_funct_1(k2_tmap_1(A_323,B_324,C_326,D_325))
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_322),u1_struct_0(B_324))
      | ~ v1_funct_1(E_321)
      | ~ m1_pre_topc(D_325,A_320)
      | v2_struct_0(D_325)
      | ~ m1_pre_topc(C_322,A_320)
      | v2_struct_0(C_322)
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320)
      | ~ l1_struct_0(D_325)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323),u1_struct_0(B_324))))
      | ~ v1_funct_2(C_326,u1_struct_0(A_323),u1_struct_0(B_324))
      | ~ v1_funct_1(C_326)
      | ~ l1_struct_0(B_324)
      | ~ l1_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_32,c_291])).

tff(c_785,plain,(
    ! [A_320,C_322,D_163,E_321] :
      ( v1_funct_1(k10_tmap_1(A_320,'#skF_2',C_322,D_163,E_321,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163))
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_322),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_321)
      | ~ m1_pre_topc(D_163,A_320)
      | v2_struct_0(D_163)
      | ~ m1_pre_topc(C_322,A_320)
      | v2_struct_0(C_322)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_163) ) ),
    inference(resolution,[status(thm)],[c_172,c_779])).

tff(c_792,plain,(
    ! [A_320,C_322,D_163,E_321] :
      ( v1_funct_1(k10_tmap_1(A_320,'#skF_2',C_322,D_163,E_321,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163))
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_322),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_321)
      | ~ m1_pre_topc(D_163,A_320)
      | v2_struct_0(D_163)
      | ~ m1_pre_topc(C_322,A_320)
      | v2_struct_0(C_322)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320)
      | ~ l1_struct_0(D_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_60,c_58,c_785])).

tff(c_794,plain,(
    ! [A_327,C_328,D_329,E_330] :
      ( v1_funct_1(k10_tmap_1(A_327,'#skF_2',C_328,D_329,E_330,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_329)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_329))
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_328),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_330,u1_struct_0(C_328),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_330)
      | ~ m1_pre_topc(D_329,A_327)
      | v2_struct_0(D_329)
      | ~ m1_pre_topc(C_328,A_327)
      | v2_struct_0(C_328)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327)
      | ~ l1_struct_0(D_329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_792])).

tff(c_803,plain,(
    ! [D_74,C_73,A_71,A_327,D_329] :
      ( v1_funct_1(k10_tmap_1(A_327,'#skF_2',D_74,D_329,k2_tmap_1(A_71,'#skF_2',C_73,D_74),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_329)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_329))
      | ~ v1_funct_2(k2_tmap_1(A_71,'#skF_2',C_73,D_74),u1_struct_0(D_74),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_71,'#skF_2',C_73,D_74))
      | ~ m1_pre_topc(D_329,A_327)
      | v2_struct_0(D_329)
      | ~ m1_pre_topc(D_74,A_327)
      | v2_struct_0(D_74)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327)
      | ~ l1_struct_0(D_329)
      | ~ l1_struct_0(D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_73)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_32,c_794])).

tff(c_822,plain,(
    ! [A_337,A_333,C_335,D_336,D_334] :
      ( v1_funct_1(k10_tmap_1(A_337,'#skF_2',D_334,D_336,k2_tmap_1(A_333,'#skF_2',C_335,D_334),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_336)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_336))
      | ~ v1_funct_2(k2_tmap_1(A_333,'#skF_2',C_335,D_334),u1_struct_0(D_334),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_333,'#skF_2',C_335,D_334))
      | ~ m1_pre_topc(D_336,A_337)
      | v2_struct_0(D_336)
      | ~ m1_pre_topc(D_334,A_337)
      | v2_struct_0(D_334)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337)
      | ~ l1_struct_0(D_336)
      | ~ l1_struct_0(D_334)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_335,u1_struct_0(A_333),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_335)
      | ~ l1_struct_0(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_803])).

tff(c_830,plain,(
    ! [A_337,D_163,D_336] :
      ( v1_funct_1(k10_tmap_1(A_337,'#skF_2',D_163,D_336,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_336)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_336))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_163))
      | ~ m1_pre_topc(D_336,A_337)
      | v2_struct_0(D_336)
      | ~ m1_pre_topc(D_163,A_337)
      | v2_struct_0(D_163)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337)
      | ~ l1_struct_0(D_336)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_163) ) ),
    inference(resolution,[status(thm)],[c_172,c_822])).

tff(c_849,plain,(
    ! [A_342,D_343,D_344] :
      ( v1_funct_1(k10_tmap_1(A_342,'#skF_2',D_343,D_344,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_343),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_344)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_344))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_343))
      | ~ m1_pre_topc(D_344,A_342)
      | v2_struct_0(D_344)
      | ~ m1_pre_topc(D_343,A_342)
      | v2_struct_0(D_343)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342)
      | ~ l1_struct_0(D_344)
      | ~ l1_struct_0(D_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_46,c_44,c_42,c_830])).

tff(c_109,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_pre_topc(k1_tsep_1(A_145,B_146,C_147),A_145)
      | ~ m1_pre_topc(C_147,A_145)
      | v2_struct_0(C_147)
      | ~ m1_pre_topc(B_146,A_145)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_115,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_109])).

tff(c_118,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_50,c_115])).

tff(c_119,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_52,c_118])).

tff(c_239,plain,(
    ! [A_197,C_194,B_196,D_198,E_195] :
      ( k3_tmap_1(A_197,B_196,C_194,D_198,E_195) = k2_partfun1(u1_struct_0(C_194),u1_struct_0(B_196),E_195,u1_struct_0(D_198))
      | ~ m1_pre_topc(D_198,C_194)
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_195,u1_struct_0(C_194),u1_struct_0(B_196))
      | ~ v1_funct_1(E_195)
      | ~ m1_pre_topc(D_198,A_197)
      | ~ m1_pre_topc(C_194,A_197)
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_243,plain,(
    ! [A_197,D_198] :
      ( k3_tmap_1(A_197,'#skF_2','#skF_1',D_198,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_198))
      | ~ m1_pre_topc(D_198,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_198,A_197)
      | ~ m1_pre_topc('#skF_1',A_197)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_42,c_239])).

tff(c_247,plain,(
    ! [A_197,D_198] :
      ( k3_tmap_1(A_197,'#skF_2','#skF_1',D_198,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_198))
      | ~ m1_pre_topc(D_198,'#skF_1')
      | ~ m1_pre_topc(D_198,A_197)
      | ~ m1_pre_topc('#skF_1',A_197)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_46,c_44,c_243])).

tff(c_249,plain,(
    ! [A_199,D_200] :
      ( k3_tmap_1(A_199,'#skF_2','#skF_1',D_200,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_200))
      | ~ m1_pre_topc(D_200,'#skF_1')
      | ~ m1_pre_topc(D_200,A_199)
      | ~ m1_pre_topc('#skF_1',A_199)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_247])).

tff(c_257,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_249])).

tff(c_269,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_119,c_50,c_257])).

tff(c_270,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_269])).

tff(c_213,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_partfun1(u1_struct_0(A_182),u1_struct_0(B_183),C_184,u1_struct_0(D_185)) = k2_tmap_1(A_182,B_183,C_184,D_185)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182),u1_struct_0(B_183))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_182),u1_struct_0(B_183))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_217,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_221,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_46,c_44,c_217])).

tff(c_222,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_221])).

tff(c_320,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_222])).

tff(c_327,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_320])).

tff(c_255,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_249])).

tff(c_265,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_119,c_54,c_255])).

tff(c_266,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_265])).

tff(c_339,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_222])).

tff(c_346,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_339])).

tff(c_611,plain,(
    ! [D_268,A_271,E_270,B_269,C_272] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_271,C_272,D_268)),u1_struct_0(B_269),E_270,k10_tmap_1(A_271,B_269,C_272,D_268,k3_tmap_1(A_271,B_269,k1_tsep_1(A_271,C_272,D_268),C_272,E_270),k3_tmap_1(A_271,B_269,k1_tsep_1(A_271,C_272,D_268),D_268,E_270)))
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_271,C_272,D_268)),u1_struct_0(B_269))))
      | ~ v1_funct_2(E_270,u1_struct_0(k1_tsep_1(A_271,C_272,D_268)),u1_struct_0(B_269))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc(D_268,A_271)
      | v2_struct_0(D_268)
      | ~ m1_pre_topc(C_272,A_271)
      | v2_struct_0(C_272)
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_616,plain,(
    ! [B_269,E_270] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_269),E_270,k10_tmap_1('#skF_1',B_269,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_269,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_270),k3_tmap_1('#skF_1',B_269,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_270)))
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_269))))
      | ~ v1_funct_2(E_270,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_269))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_611])).

tff(c_625,plain,(
    ! [B_269,E_270] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_269),E_270,k10_tmap_1('#skF_1',B_269,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_269,'#skF_1','#skF_3',E_270),k3_tmap_1('#skF_1',B_269,'#skF_1','#skF_4',E_270)))
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_269))))
      | ~ v1_funct_2(E_270,u1_struct_0('#skF_1'),u1_struct_0(B_269))
      | ~ v1_funct_1(E_270)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_50,c_48,c_48,c_48,c_48,c_616])).

tff(c_633,plain,(
    ! [B_273,E_274] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_273),E_274,k10_tmap_1('#skF_1',B_273,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_273,'#skF_1','#skF_3',E_274),k3_tmap_1('#skF_1',B_273,'#skF_1','#skF_4',E_274)))
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_273))))
      | ~ v1_funct_2(E_274,u1_struct_0('#skF_1'),u1_struct_0(B_273))
      | ~ v1_funct_1(E_274)
      | ~ l1_pre_topc(B_273)
      | ~ v2_pre_topc(B_273)
      | v2_struct_0(B_273) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_52,c_625])).

tff(c_638,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_633])).

tff(c_644,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_46,c_44,c_42,c_327,c_638])).

tff(c_645,plain,(
    r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_644])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_650,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_645,c_4])).

tff(c_653,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_650])).

tff(c_655,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_852,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_849,c_655])).

tff(c_855,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_66,c_64,c_54,c_50,c_852])).

tff(c_856,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_52,c_855])).

tff(c_857,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_860,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_857])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_860])).

tff(c_866,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_865,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_867,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_881,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_867])).

tff(c_885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_881])).

tff(c_886,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_890,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_886])).

tff(c_894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_890])).

tff(c_895,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_902,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_905,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_526,c_902])).

tff(c_908,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_905])).

tff(c_909,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_908])).

tff(c_910,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_909])).

tff(c_914,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_910])).

tff(c_922,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_914])).

tff(c_926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_922])).

tff(c_927,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_929,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_933,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_929])).

tff(c_936,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_933])).

tff(c_939,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_936])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_939])).

tff(c_945,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1004,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_945,c_2])).

tff(c_1005,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1004])).

tff(c_1009,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_1005])).

tff(c_1017,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1009])).

tff(c_1021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1017])).

tff(c_1023,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_1022,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_1024,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1022])).

tff(c_1031,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_1024])).

tff(c_1034,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1031])).

tff(c_1038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1034])).

tff(c_1040,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1022])).

tff(c_944,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_1092,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1040,c_944])).

tff(c_1093,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_1097,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_1093])).

tff(c_1100,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_1104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1100])).

tff(c_1105,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_1144,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1105])).

tff(c_1147,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_1144])).

tff(c_1150,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1147])).

tff(c_1154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1150])).

tff(c_1155,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_1209,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1155])).

tff(c_1228,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1225,c_1209])).

tff(c_1238,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_60,c_58,c_1228])).

tff(c_1239,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1238])).

tff(c_1246,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_1274,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_1246])).

tff(c_1277,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1274])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1277])).

tff(c_1282,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_1284,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1287,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_1284])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1287])).

tff(c_1293,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_192,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( m1_subset_1(k2_tmap_1(A_172,B_173,C_174,D_175),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_175),u1_struct_0(B_173))))
      | ~ l1_struct_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_struct_0(B_173)
      | ~ l1_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_36,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( v1_funct_1(k2_tmap_1(A_71,B_72,C_73,D_74))
      | ~ l1_struct_0(D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0(B_72))
      | ~ v1_funct_1(C_73)
      | ~ l1_struct_0(B_72)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_203,plain,(
    ! [D_74,D_175,A_172,C_174,B_173] :
      ( v1_funct_1(k2_tmap_1(D_175,B_173,k2_tmap_1(A_172,B_173,C_174,D_175),D_74))
      | ~ l1_struct_0(D_74)
      | ~ v1_funct_2(k2_tmap_1(A_172,B_173,C_174,D_175),u1_struct_0(D_175),u1_struct_0(B_173))
      | ~ v1_funct_1(k2_tmap_1(A_172,B_173,C_174,D_175))
      | ~ l1_struct_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_struct_0(B_173)
      | ~ l1_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_192,c_36])).

tff(c_1297,plain,(
    ! [D_74] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_74))
      | ~ l1_struct_0(D_74)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1293,c_203])).

tff(c_1304,plain,(
    ! [D_74] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_74))
      | ~ l1_struct_0(D_74)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_1224,c_1297])).

tff(c_1305,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1304])).

tff(c_1308,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_1305])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1308])).

tff(c_1314,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1304])).

tff(c_1292,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1341,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1292])).

tff(c_1342,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_1349,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_1342])).

tff(c_1352,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1349])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1352])).

tff(c_1357,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_1372,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1357])).

tff(c_1375,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_158,c_46,c_44,c_42,c_1372])).

tff(c_1378,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1375])).

tff(c_1382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1378])).

tff(c_1383,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_40,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_69,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_1393,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_69])).

tff(c_1435,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_189,c_1393])).

tff(c_1438,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1435])).

tff(c_1440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_1438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.79/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.05  
% 8.97/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.05  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.97/3.05  
% 8.97/3.05  %Foreground sorts:
% 8.97/3.05  
% 8.97/3.05  
% 8.97/3.05  %Background operators:
% 8.97/3.05  
% 8.97/3.05  
% 8.97/3.05  %Foreground operators:
% 8.97/3.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.97/3.05  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.97/3.05  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.97/3.05  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.97/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.97/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.97/3.05  tff('#skF_5', type, '#skF_5': $i).
% 8.97/3.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.97/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.97/3.05  tff('#skF_3', type, '#skF_3': $i).
% 8.97/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.97/3.05  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.97/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.97/3.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.97/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/3.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.97/3.05  tff('#skF_4', type, '#skF_4': $i).
% 8.97/3.05  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 8.97/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/3.05  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.97/3.05  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.97/3.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.97/3.05  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.97/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.97/3.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.97/3.05  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.97/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.97/3.05  
% 8.97/3.11  tff(f_298, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_tmap_1)).
% 8.97/3.11  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.97/3.11  tff(f_223, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 8.97/3.11  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 8.97/3.11  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.97/3.11  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.97/3.11  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 8.97/3.11  tff(f_205, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 8.97/3.11  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 8.97/3.11  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.97/3.11  tff(f_259, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_tmap_1)).
% 8.97/3.11  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.97/3.11  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.97/3.11  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_133, plain, (![A_151, B_152, C_153, D_154]: (v1_funct_1(k2_tmap_1(A_151, B_152, C_153, D_154)) | ~l1_struct_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151), u1_struct_0(B_152)))) | ~v1_funct_2(C_153, u1_struct_0(A_151), u1_struct_0(B_152)) | ~v1_funct_1(C_153) | ~l1_struct_0(B_152) | ~l1_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.97/3.11  tff(c_135, plain, (![D_154]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~l1_struct_0(D_154) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_133])).
% 8.97/3.11  tff(c_138, plain, (![D_154]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~l1_struct_0(D_154) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_135])).
% 8.97/3.11  tff(c_139, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_138])).
% 8.97/3.11  tff(c_142, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_139])).
% 8.97/3.11  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_142])).
% 8.97/3.11  tff(c_147, plain, (![D_154]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~l1_struct_0(D_154))), inference(splitRight, [status(thm)], [c_138])).
% 8.97/3.11  tff(c_149, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_147])).
% 8.97/3.11  tff(c_152, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_149])).
% 8.97/3.11  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_152])).
% 8.97/3.11  tff(c_158, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_147])).
% 8.97/3.11  tff(c_174, plain, (![C_169, A_166, F_168, D_167, B_165]: (r1_funct_2(A_166, B_165, C_169, D_167, F_168, F_168) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_169, D_167))) | ~v1_funct_2(F_168, C_169, D_167) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))) | ~v1_funct_2(F_168, A_166, B_165) | ~v1_funct_1(F_168) | v1_xboole_0(D_167) | v1_xboole_0(B_165))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.97/3.11  tff(c_176, plain, (![A_166, B_165]: (r1_funct_2(A_166, B_165, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))) | ~v1_funct_2('#skF_5', A_166, B_165) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_165))), inference(resolution, [status(thm)], [c_42, c_174])).
% 8.97/3.11  tff(c_179, plain, (![A_166, B_165]: (r1_funct_2(A_166, B_165, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))) | ~v1_funct_2('#skF_5', A_166, B_165) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_165))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_176])).
% 8.97/3.11  tff(c_180, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_179])).
% 8.97/3.11  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.97/3.11  tff(c_183, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_180, c_10])).
% 8.97/3.11  tff(c_186, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_183])).
% 8.97/3.11  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_186])).
% 8.97/3.11  tff(c_190, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_179])).
% 8.97/3.11  tff(c_189, plain, (![A_166, B_165]: (r1_funct_2(A_166, B_165, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))) | ~v1_funct_2('#skF_5', A_166, B_165) | v1_xboole_0(B_165))), inference(splitRight, [status(thm)], [c_179])).
% 8.97/3.11  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_75, plain, (![B_133, A_134]: (l1_pre_topc(B_133) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.97/3.11  tff(c_78, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_75])).
% 8.97/3.11  tff(c_84, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_78])).
% 8.97/3.11  tff(c_148, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_138])).
% 8.97/3.11  tff(c_32, plain, (![A_71, B_72, C_73, D_74]: (m1_subset_1(k2_tmap_1(A_71, B_72, C_73, D_74), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_74), u1_struct_0(B_72)))) | ~l1_struct_0(D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_72)))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0(B_72)) | ~v1_funct_1(C_73) | ~l1_struct_0(B_72) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.97/3.11  tff(c_167, plain, (![A_160, B_161, C_162, D_163]: (v1_funct_2(k2_tmap_1(A_160, B_161, C_162, D_163), u1_struct_0(D_163), u1_struct_0(B_161)) | ~l1_struct_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160), u1_struct_0(B_161)))) | ~v1_funct_2(C_162, u1_struct_0(A_160), u1_struct_0(B_161)) | ~v1_funct_1(C_162) | ~l1_struct_0(B_161) | ~l1_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.97/3.11  tff(c_169, plain, (![D_163]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~l1_struct_0(D_163) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_167])).
% 8.97/3.11  tff(c_172, plain, (![D_163]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~l1_struct_0(D_163))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_169])).
% 8.97/3.11  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_81, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_75])).
% 8.97/3.11  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_81])).
% 8.97/3.11  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_48, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_389, plain, (![A_209, B_210, D_212, E_207, F_211, C_208]: (v1_funct_2(k10_tmap_1(A_209, B_210, C_208, D_212, E_207, F_211), u1_struct_0(k1_tsep_1(A_209, C_208, D_212)), u1_struct_0(B_210)) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_212), u1_struct_0(B_210)))) | ~v1_funct_2(F_211, u1_struct_0(D_212), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_208), u1_struct_0(B_210)))) | ~v1_funct_2(E_207, u1_struct_0(C_208), u1_struct_0(B_210)) | ~v1_funct_1(E_207) | ~m1_pre_topc(D_212, A_209) | v2_struct_0(D_212) | ~m1_pre_topc(C_208, A_209) | v2_struct_0(C_208) | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.97/3.11  tff(c_392, plain, (![B_210, E_207, F_211]: (v1_funct_2(k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_207, F_211), u1_struct_0('#skF_1'), u1_struct_0(B_210)) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_210)))) | ~v1_funct_2(F_211, u1_struct_0('#skF_4'), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_210)))) | ~v1_funct_2(E_207, u1_struct_0('#skF_3'), u1_struct_0(B_210)) | ~v1_funct_1(E_207) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_389])).
% 8.97/3.11  tff(c_394, plain, (![B_210, E_207, F_211]: (v1_funct_2(k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_207, F_211), u1_struct_0('#skF_1'), u1_struct_0(B_210)) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_210)))) | ~v1_funct_2(F_211, u1_struct_0('#skF_4'), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_210)))) | ~v1_funct_2(E_207, u1_struct_0('#skF_3'), u1_struct_0(B_210)) | ~v1_funct_1(E_207) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_50, c_392])).
% 8.97/3.11  tff(c_439, plain, (![B_220, E_221, F_222]: (v1_funct_2(k10_tmap_1('#skF_1', B_220, '#skF_3', '#skF_4', E_221, F_222), u1_struct_0('#skF_1'), u1_struct_0(B_220)) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_220)))) | ~v1_funct_2(F_222, u1_struct_0('#skF_4'), u1_struct_0(B_220)) | ~v1_funct_1(F_222) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_220)))) | ~v1_funct_2(E_221, u1_struct_0('#skF_3'), u1_struct_0(B_220)) | ~v1_funct_1(E_221) | ~l1_pre_topc(B_220) | ~v2_pre_topc(B_220) | v2_struct_0(B_220))), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_52, c_394])).
% 8.97/3.11  tff(c_443, plain, (![B_72, E_221, A_71, C_73]: (v1_funct_2(k10_tmap_1('#skF_1', B_72, '#skF_3', '#skF_4', E_221, k2_tmap_1(A_71, B_72, C_73, '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0(B_72)) | ~v1_funct_2(k2_tmap_1(A_71, B_72, C_73, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(B_72)) | ~v1_funct_1(k2_tmap_1(A_71, B_72, C_73, '#skF_4')) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_72)))) | ~v1_funct_2(E_221, u1_struct_0('#skF_3'), u1_struct_0(B_72)) | ~v1_funct_1(E_221) | ~l1_pre_topc(B_72) | ~v2_pre_topc(B_72) | v2_struct_0(B_72) | ~l1_struct_0('#skF_4') | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_72)))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0(B_72)) | ~v1_funct_1(C_73) | ~l1_struct_0(B_72) | ~l1_struct_0(A_71))), inference(resolution, [status(thm)], [c_32, c_439])).
% 8.97/3.11  tff(c_1215, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_443])).
% 8.97/3.11  tff(c_1218, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_1215])).
% 8.97/3.11  tff(c_1222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1218])).
% 8.97/3.11  tff(c_1224, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_443])).
% 8.97/3.11  tff(c_157, plain, (![D_154]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~l1_struct_0(D_154))), inference(splitRight, [status(thm)], [c_147])).
% 8.97/3.11  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_1225, plain, (![B_402, E_403, A_404, C_405]: (v1_funct_2(k10_tmap_1('#skF_1', B_402, '#skF_3', '#skF_4', E_403, k2_tmap_1(A_404, B_402, C_405, '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0(B_402)) | ~v1_funct_2(k2_tmap_1(A_404, B_402, C_405, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(B_402)) | ~v1_funct_1(k2_tmap_1(A_404, B_402, C_405, '#skF_4')) | ~m1_subset_1(E_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_402)))) | ~v1_funct_2(E_403, u1_struct_0('#skF_3'), u1_struct_0(B_402)) | ~v1_funct_1(E_403) | ~l1_pre_topc(B_402) | ~v2_pre_topc(B_402) | v2_struct_0(B_402) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), u1_struct_0(B_402)))) | ~v1_funct_2(C_405, u1_struct_0(A_404), u1_struct_0(B_402)) | ~v1_funct_1(C_405) | ~l1_struct_0(B_402) | ~l1_struct_0(A_404))), inference(splitRight, [status(thm)], [c_443])).
% 8.97/3.11  tff(c_492, plain, (![B_237, D_239, E_234, C_235, F_238, A_236]: (m1_subset_1(k10_tmap_1(A_236, B_237, C_235, D_239, E_234, F_238), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_236, C_235, D_239)), u1_struct_0(B_237)))) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_239), u1_struct_0(B_237)))) | ~v1_funct_2(F_238, u1_struct_0(D_239), u1_struct_0(B_237)) | ~v1_funct_1(F_238) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_235), u1_struct_0(B_237)))) | ~v1_funct_2(E_234, u1_struct_0(C_235), u1_struct_0(B_237)) | ~v1_funct_1(E_234) | ~m1_pre_topc(D_239, A_236) | v2_struct_0(D_239) | ~m1_pre_topc(C_235, A_236) | v2_struct_0(C_235) | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.97/3.11  tff(c_512, plain, (![B_237, E_234, F_238]: (m1_subset_1(k10_tmap_1('#skF_1', B_237, '#skF_3', '#skF_4', E_234, F_238), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_237)))) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_237)))) | ~v1_funct_2(F_238, u1_struct_0('#skF_4'), u1_struct_0(B_237)) | ~v1_funct_1(F_238) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_237)))) | ~v1_funct_2(E_234, u1_struct_0('#skF_3'), u1_struct_0(B_237)) | ~v1_funct_1(E_234) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_492])).
% 8.97/3.11  tff(c_525, plain, (![B_237, E_234, F_238]: (m1_subset_1(k10_tmap_1('#skF_1', B_237, '#skF_3', '#skF_4', E_234, F_238), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_237)))) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_237)))) | ~v1_funct_2(F_238, u1_struct_0('#skF_4'), u1_struct_0(B_237)) | ~v1_funct_1(F_238) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_237)))) | ~v1_funct_2(E_234, u1_struct_0('#skF_3'), u1_struct_0(B_237)) | ~v1_funct_1(E_234) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_50, c_512])).
% 8.97/3.11  tff(c_526, plain, (![B_237, E_234, F_238]: (m1_subset_1(k10_tmap_1('#skF_1', B_237, '#skF_3', '#skF_4', E_234, F_238), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_237)))) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_237)))) | ~v1_funct_2(F_238, u1_struct_0('#skF_4'), u1_struct_0(B_237)) | ~v1_funct_1(F_238) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_237)))) | ~v1_funct_2(E_234, u1_struct_0('#skF_3'), u1_struct_0(B_237)) | ~v1_funct_1(E_234) | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237))), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_52, c_525])).
% 8.97/3.11  tff(c_656, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_443])).
% 8.97/3.11  tff(c_659, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_656])).
% 8.97/3.11  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_659])).
% 8.97/3.11  tff(c_665, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_443])).
% 8.97/3.11  tff(c_291, plain, (![B_204, E_201, A_203, C_202, F_205, D_206]: (v1_funct_1(k10_tmap_1(A_203, B_204, C_202, D_206, E_201, F_205)) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206), u1_struct_0(B_204)))) | ~v1_funct_2(F_205, u1_struct_0(D_206), u1_struct_0(B_204)) | ~v1_funct_1(F_205) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202), u1_struct_0(B_204)))) | ~v1_funct_2(E_201, u1_struct_0(C_202), u1_struct_0(B_204)) | ~v1_funct_1(E_201) | ~m1_pre_topc(D_206, A_203) | v2_struct_0(D_206) | ~m1_pre_topc(C_202, A_203) | v2_struct_0(C_202) | ~l1_pre_topc(B_204) | ~v2_pre_topc(B_204) | v2_struct_0(B_204) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.97/3.11  tff(c_779, plain, (![C_326, C_322, A_320, D_325, B_324, E_321, A_323]: (v1_funct_1(k10_tmap_1(A_320, B_324, C_322, D_325, E_321, k2_tmap_1(A_323, B_324, C_326, D_325))) | ~v1_funct_2(k2_tmap_1(A_323, B_324, C_326, D_325), u1_struct_0(D_325), u1_struct_0(B_324)) | ~v1_funct_1(k2_tmap_1(A_323, B_324, C_326, D_325)) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322), u1_struct_0(B_324)))) | ~v1_funct_2(E_321, u1_struct_0(C_322), u1_struct_0(B_324)) | ~v1_funct_1(E_321) | ~m1_pre_topc(D_325, A_320) | v2_struct_0(D_325) | ~m1_pre_topc(C_322, A_320) | v2_struct_0(C_322) | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320) | ~l1_struct_0(D_325) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323), u1_struct_0(B_324)))) | ~v1_funct_2(C_326, u1_struct_0(A_323), u1_struct_0(B_324)) | ~v1_funct_1(C_326) | ~l1_struct_0(B_324) | ~l1_struct_0(A_323))), inference(resolution, [status(thm)], [c_32, c_291])).
% 8.97/3.11  tff(c_785, plain, (![A_320, C_322, D_163, E_321]: (v1_funct_1(k10_tmap_1(A_320, '#skF_2', C_322, D_163, E_321, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163)) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_321, u1_struct_0(C_322), u1_struct_0('#skF_2')) | ~v1_funct_1(E_321) | ~m1_pre_topc(D_163, A_320) | v2_struct_0(D_163) | ~m1_pre_topc(C_322, A_320) | v2_struct_0(C_322) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_163))), inference(resolution, [status(thm)], [c_172, c_779])).
% 8.97/3.11  tff(c_792, plain, (![A_320, C_322, D_163, E_321]: (v1_funct_1(k10_tmap_1(A_320, '#skF_2', C_322, D_163, E_321, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163)) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_321, u1_struct_0(C_322), u1_struct_0('#skF_2')) | ~v1_funct_1(E_321) | ~m1_pre_topc(D_163, A_320) | v2_struct_0(D_163) | ~m1_pre_topc(C_322, A_320) | v2_struct_0(C_322) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320) | ~l1_struct_0(D_163))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_60, c_58, c_785])).
% 8.97/3.11  tff(c_794, plain, (![A_327, C_328, D_329, E_330]: (v1_funct_1(k10_tmap_1(A_327, '#skF_2', C_328, D_329, E_330, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_329))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_329)) | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_328), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_330, u1_struct_0(C_328), u1_struct_0('#skF_2')) | ~v1_funct_1(E_330) | ~m1_pre_topc(D_329, A_327) | v2_struct_0(D_329) | ~m1_pre_topc(C_328, A_327) | v2_struct_0(C_328) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327) | ~l1_struct_0(D_329))), inference(negUnitSimplification, [status(thm)], [c_62, c_792])).
% 8.97/3.11  tff(c_803, plain, (![D_74, C_73, A_71, A_327, D_329]: (v1_funct_1(k10_tmap_1(A_327, '#skF_2', D_74, D_329, k2_tmap_1(A_71, '#skF_2', C_73, D_74), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_329))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_329)) | ~v1_funct_2(k2_tmap_1(A_71, '#skF_2', C_73, D_74), u1_struct_0(D_74), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_71, '#skF_2', C_73, D_74)) | ~m1_pre_topc(D_329, A_327) | v2_struct_0(D_329) | ~m1_pre_topc(D_74, A_327) | v2_struct_0(D_74) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327) | ~l1_struct_0(D_329) | ~l1_struct_0(D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0('#skF_2')) | ~v1_funct_1(C_73) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_71))), inference(resolution, [status(thm)], [c_32, c_794])).
% 8.97/3.11  tff(c_822, plain, (![A_337, A_333, C_335, D_336, D_334]: (v1_funct_1(k10_tmap_1(A_337, '#skF_2', D_334, D_336, k2_tmap_1(A_333, '#skF_2', C_335, D_334), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_336))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_336)) | ~v1_funct_2(k2_tmap_1(A_333, '#skF_2', C_335, D_334), u1_struct_0(D_334), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_333, '#skF_2', C_335, D_334)) | ~m1_pre_topc(D_336, A_337) | v2_struct_0(D_336) | ~m1_pre_topc(D_334, A_337) | v2_struct_0(D_334) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337) | v2_struct_0(A_337) | ~l1_struct_0(D_336) | ~l1_struct_0(D_334) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_335, u1_struct_0(A_333), u1_struct_0('#skF_2')) | ~v1_funct_1(C_335) | ~l1_struct_0(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_803])).
% 8.97/3.11  tff(c_830, plain, (![A_337, D_163, D_336]: (v1_funct_1(k10_tmap_1(A_337, '#skF_2', D_163, D_336, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_336))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_336)) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_163)) | ~m1_pre_topc(D_336, A_337) | v2_struct_0(D_336) | ~m1_pre_topc(D_163, A_337) | v2_struct_0(D_163) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337) | v2_struct_0(A_337) | ~l1_struct_0(D_336) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_163))), inference(resolution, [status(thm)], [c_172, c_822])).
% 8.97/3.11  tff(c_849, plain, (![A_342, D_343, D_344]: (v1_funct_1(k10_tmap_1(A_342, '#skF_2', D_343, D_344, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_343), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_344))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_344)) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_343)) | ~m1_pre_topc(D_344, A_342) | v2_struct_0(D_344) | ~m1_pre_topc(D_343, A_342) | v2_struct_0(D_343) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342) | ~l1_struct_0(D_344) | ~l1_struct_0(D_343))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_46, c_44, c_42, c_830])).
% 8.97/3.11  tff(c_109, plain, (![A_145, B_146, C_147]: (m1_pre_topc(k1_tsep_1(A_145, B_146, C_147), A_145) | ~m1_pre_topc(C_147, A_145) | v2_struct_0(C_147) | ~m1_pre_topc(B_146, A_145) | v2_struct_0(B_146) | ~l1_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_205])).
% 8.97/3.11  tff(c_115, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_109])).
% 8.97/3.11  tff(c_118, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_50, c_115])).
% 8.97/3.11  tff(c_119, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_52, c_118])).
% 8.97/3.11  tff(c_239, plain, (![A_197, C_194, B_196, D_198, E_195]: (k3_tmap_1(A_197, B_196, C_194, D_198, E_195)=k2_partfun1(u1_struct_0(C_194), u1_struct_0(B_196), E_195, u1_struct_0(D_198)) | ~m1_pre_topc(D_198, C_194) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194), u1_struct_0(B_196)))) | ~v1_funct_2(E_195, u1_struct_0(C_194), u1_struct_0(B_196)) | ~v1_funct_1(E_195) | ~m1_pre_topc(D_198, A_197) | ~m1_pre_topc(C_194, A_197) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.97/3.11  tff(c_243, plain, (![A_197, D_198]: (k3_tmap_1(A_197, '#skF_2', '#skF_1', D_198, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_198)) | ~m1_pre_topc(D_198, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_198, A_197) | ~m1_pre_topc('#skF_1', A_197) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_42, c_239])).
% 8.97/3.11  tff(c_247, plain, (![A_197, D_198]: (k3_tmap_1(A_197, '#skF_2', '#skF_1', D_198, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_198)) | ~m1_pre_topc(D_198, '#skF_1') | ~m1_pre_topc(D_198, A_197) | ~m1_pre_topc('#skF_1', A_197) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_46, c_44, c_243])).
% 8.97/3.11  tff(c_249, plain, (![A_199, D_200]: (k3_tmap_1(A_199, '#skF_2', '#skF_1', D_200, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_200)) | ~m1_pre_topc(D_200, '#skF_1') | ~m1_pre_topc(D_200, A_199) | ~m1_pre_topc('#skF_1', A_199) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(negUnitSimplification, [status(thm)], [c_62, c_247])).
% 8.97/3.11  tff(c_257, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_249])).
% 8.97/3.11  tff(c_269, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_119, c_50, c_257])).
% 8.97/3.11  tff(c_270, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_269])).
% 8.97/3.11  tff(c_213, plain, (![A_182, B_183, C_184, D_185]: (k2_partfun1(u1_struct_0(A_182), u1_struct_0(B_183), C_184, u1_struct_0(D_185))=k2_tmap_1(A_182, B_183, C_184, D_185) | ~m1_pre_topc(D_185, A_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182), u1_struct_0(B_183)))) | ~v1_funct_2(C_184, u1_struct_0(A_182), u1_struct_0(B_183)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_183) | ~v2_pre_topc(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.97/3.11  tff(c_217, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_185) | ~m1_pre_topc(D_185, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_213])).
% 8.97/3.11  tff(c_221, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_185) | ~m1_pre_topc(D_185, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_46, c_44, c_217])).
% 8.97/3.11  tff(c_222, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_185) | ~m1_pre_topc(D_185, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_221])).
% 8.97/3.11  tff(c_320, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_270, c_222])).
% 8.97/3.11  tff(c_327, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_320])).
% 8.97/3.11  tff(c_255, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_249])).
% 8.97/3.11  tff(c_265, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_119, c_54, c_255])).
% 8.97/3.11  tff(c_266, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_265])).
% 8.97/3.11  tff(c_339, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_222])).
% 8.97/3.11  tff(c_346, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_339])).
% 8.97/3.11  tff(c_611, plain, (![D_268, A_271, E_270, B_269, C_272]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_271, C_272, D_268)), u1_struct_0(B_269), E_270, k10_tmap_1(A_271, B_269, C_272, D_268, k3_tmap_1(A_271, B_269, k1_tsep_1(A_271, C_272, D_268), C_272, E_270), k3_tmap_1(A_271, B_269, k1_tsep_1(A_271, C_272, D_268), D_268, E_270))) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_271, C_272, D_268)), u1_struct_0(B_269)))) | ~v1_funct_2(E_270, u1_struct_0(k1_tsep_1(A_271, C_272, D_268)), u1_struct_0(B_269)) | ~v1_funct_1(E_270) | ~m1_pre_topc(D_268, A_271) | v2_struct_0(D_268) | ~m1_pre_topc(C_272, A_271) | v2_struct_0(C_272) | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.97/3.11  tff(c_616, plain, (![B_269, E_270]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_269), E_270, k10_tmap_1('#skF_1', B_269, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_269, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_270), k3_tmap_1('#skF_1', B_269, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_270))) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_269)))) | ~v1_funct_2(E_270, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_269)) | ~v1_funct_1(E_270) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_611])).
% 8.97/3.11  tff(c_625, plain, (![B_269, E_270]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_269), E_270, k10_tmap_1('#skF_1', B_269, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_269, '#skF_1', '#skF_3', E_270), k3_tmap_1('#skF_1', B_269, '#skF_1', '#skF_4', E_270))) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_269)))) | ~v1_funct_2(E_270, u1_struct_0('#skF_1'), u1_struct_0(B_269)) | ~v1_funct_1(E_270) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_50, c_48, c_48, c_48, c_48, c_616])).
% 8.97/3.11  tff(c_633, plain, (![B_273, E_274]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_273), E_274, k10_tmap_1('#skF_1', B_273, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_273, '#skF_1', '#skF_3', E_274), k3_tmap_1('#skF_1', B_273, '#skF_1', '#skF_4', E_274))) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_273)))) | ~v1_funct_2(E_274, u1_struct_0('#skF_1'), u1_struct_0(B_273)) | ~v1_funct_1(E_274) | ~l1_pre_topc(B_273) | ~v2_pre_topc(B_273) | v2_struct_0(B_273))), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_52, c_625])).
% 8.97/3.11  tff(c_638, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_346, c_633])).
% 8.97/3.11  tff(c_644, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_46, c_44, c_42, c_327, c_638])).
% 8.97/3.11  tff(c_645, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_644])).
% 8.97/3.11  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.97/3.11  tff(c_650, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_645, c_4])).
% 8.97/3.11  tff(c_653, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_650])).
% 8.97/3.11  tff(c_655, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_653])).
% 8.97/3.11  tff(c_852, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_849, c_655])).
% 8.97/3.11  tff(c_855, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_66, c_64, c_54, c_50, c_852])).
% 8.97/3.11  tff(c_856, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_52, c_855])).
% 8.97/3.11  tff(c_857, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_856])).
% 8.97/3.11  tff(c_860, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_857])).
% 8.97/3.11  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_860])).
% 8.97/3.11  tff(c_866, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_856])).
% 8.97/3.11  tff(c_865, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_856])).
% 8.97/3.11  tff(c_867, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_865])).
% 8.97/3.11  tff(c_881, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_157, c_867])).
% 8.97/3.11  tff(c_885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_665, c_881])).
% 8.97/3.11  tff(c_886, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_865])).
% 8.97/3.11  tff(c_890, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_157, c_886])).
% 8.97/3.11  tff(c_894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_866, c_890])).
% 8.97/3.11  tff(c_895, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_653])).
% 8.97/3.11  tff(c_902, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_895])).
% 8.97/3.11  tff(c_905, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_526, c_902])).
% 8.97/3.11  tff(c_908, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_905])).
% 8.97/3.11  tff(c_909, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_908])).
% 8.97/3.11  tff(c_910, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_909])).
% 8.97/3.11  tff(c_914, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_157, c_910])).
% 8.97/3.11  tff(c_922, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_914])).
% 8.97/3.11  tff(c_926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_922])).
% 8.97/3.11  tff(c_927, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_909])).
% 8.97/3.11  tff(c_929, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_927])).
% 8.97/3.11  tff(c_933, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_929])).
% 8.97/3.11  tff(c_936, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_933])).
% 8.97/3.11  tff(c_939, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_936])).
% 8.97/3.11  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_939])).
% 8.97/3.11  tff(c_945, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_927])).
% 8.97/3.11  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.97/3.11  tff(c_1004, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_945, c_2])).
% 8.97/3.11  tff(c_1005, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1004])).
% 8.97/3.11  tff(c_1009, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_157, c_1005])).
% 8.97/3.11  tff(c_1017, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_1009])).
% 8.97/3.11  tff(c_1021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1017])).
% 8.97/3.11  tff(c_1023, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1004])).
% 8.97/3.11  tff(c_1022, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1004])).
% 8.97/3.11  tff(c_1024, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1022])).
% 8.97/3.11  tff(c_1031, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_172, c_1024])).
% 8.97/3.11  tff(c_1034, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_1031])).
% 8.97/3.11  tff(c_1038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1034])).
% 8.97/3.11  tff(c_1040, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1022])).
% 8.97/3.11  tff(c_944, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_927])).
% 8.97/3.11  tff(c_1092, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1040, c_944])).
% 8.97/3.11  tff(c_1093, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1092])).
% 8.97/3.11  tff(c_1097, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_172, c_1093])).
% 8.97/3.11  tff(c_1100, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1097])).
% 8.97/3.11  tff(c_1104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1100])).
% 8.97/3.11  tff(c_1105, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1092])).
% 8.97/3.11  tff(c_1144, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1105])).
% 8.97/3.11  tff(c_1147, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_1144])).
% 8.97/3.11  tff(c_1150, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1147])).
% 8.97/3.11  tff(c_1154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1150])).
% 8.97/3.11  tff(c_1155, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_895])).
% 8.97/3.11  tff(c_1209, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1155])).
% 8.97/3.11  tff(c_1228, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1225, c_1209])).
% 8.97/3.11  tff(c_1238, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_60, c_58, c_1228])).
% 8.97/3.11  tff(c_1239, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1238])).
% 8.97/3.11  tff(c_1246, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1239])).
% 8.97/3.11  tff(c_1274, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_157, c_1246])).
% 8.97/3.11  tff(c_1277, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1274])).
% 8.97/3.11  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1277])).
% 8.97/3.11  tff(c_1282, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1239])).
% 8.97/3.11  tff(c_1284, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1282])).
% 8.97/3.11  tff(c_1287, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_172, c_1284])).
% 8.97/3.11  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_1287])).
% 8.97/3.11  tff(c_1293, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1282])).
% 8.97/3.11  tff(c_192, plain, (![A_172, B_173, C_174, D_175]: (m1_subset_1(k2_tmap_1(A_172, B_173, C_174, D_175), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_175), u1_struct_0(B_173)))) | ~l1_struct_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0(A_172), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_struct_0(B_173) | ~l1_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.97/3.11  tff(c_36, plain, (![A_71, B_72, C_73, D_74]: (v1_funct_1(k2_tmap_1(A_71, B_72, C_73, D_74)) | ~l1_struct_0(D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_72)))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0(B_72)) | ~v1_funct_1(C_73) | ~l1_struct_0(B_72) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.97/3.11  tff(c_203, plain, (![D_74, D_175, A_172, C_174, B_173]: (v1_funct_1(k2_tmap_1(D_175, B_173, k2_tmap_1(A_172, B_173, C_174, D_175), D_74)) | ~l1_struct_0(D_74) | ~v1_funct_2(k2_tmap_1(A_172, B_173, C_174, D_175), u1_struct_0(D_175), u1_struct_0(B_173)) | ~v1_funct_1(k2_tmap_1(A_172, B_173, C_174, D_175)) | ~l1_struct_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0(A_172), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_struct_0(B_173) | ~l1_struct_0(A_172))), inference(resolution, [status(thm)], [c_192, c_36])).
% 8.97/3.11  tff(c_1297, plain, (![D_74]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_74)) | ~l1_struct_0(D_74) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1293, c_203])).
% 8.97/3.11  tff(c_1304, plain, (![D_74]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_74)) | ~l1_struct_0(D_74) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_1224, c_1297])).
% 8.97/3.11  tff(c_1305, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1304])).
% 8.97/3.11  tff(c_1308, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_157, c_1305])).
% 8.97/3.11  tff(c_1312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_1308])).
% 8.97/3.11  tff(c_1314, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1304])).
% 8.97/3.11  tff(c_1292, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1282])).
% 8.97/3.11  tff(c_1341, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1292])).
% 8.97/3.11  tff(c_1342, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1341])).
% 8.97/3.11  tff(c_1349, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_172, c_1342])).
% 8.97/3.11  tff(c_1352, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1349])).
% 8.97/3.11  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1352])).
% 8.97/3.11  tff(c_1357, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1341])).
% 8.97/3.11  tff(c_1372, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1357])).
% 8.97/3.11  tff(c_1375, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_158, c_46, c_44, c_42, c_1372])).
% 8.97/3.11  tff(c_1378, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1375])).
% 8.97/3.11  tff(c_1382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1378])).
% 8.97/3.11  tff(c_1383, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_1155])).
% 8.97/3.11  tff(c_40, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_298])).
% 8.97/3.11  tff(c_69, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 8.97/3.11  tff(c_1393, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_69])).
% 8.97/3.11  tff(c_1435, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_189, c_1393])).
% 8.97/3.11  tff(c_1438, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1435])).
% 8.97/3.11  tff(c_1440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_1438])).
% 8.97/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.11  
% 8.97/3.11  Inference rules
% 8.97/3.11  ----------------------
% 8.97/3.11  #Ref     : 0
% 8.97/3.11  #Sup     : 248
% 8.97/3.11  #Fact    : 0
% 8.97/3.11  #Define  : 0
% 8.97/3.11  #Split   : 21
% 8.97/3.11  #Chain   : 0
% 8.97/3.11  #Close   : 0
% 8.97/3.11  
% 8.97/3.11  Ordering : KBO
% 8.97/3.11  
% 8.97/3.11  Simplification rules
% 8.97/3.11  ----------------------
% 8.97/3.11  #Subsume      : 20
% 8.97/3.11  #Demod        : 486
% 8.97/3.11  #Tautology    : 68
% 8.97/3.11  #SimpNegUnit  : 77
% 8.97/3.11  #BackRed      : 7
% 8.97/3.11  
% 8.97/3.11  #Partial instantiations: 0
% 8.97/3.11  #Strategies tried      : 1
% 8.97/3.11  
% 8.97/3.11  Timing (in seconds)
% 8.97/3.11  ----------------------
% 8.97/3.12  Preprocessing        : 0.65
% 8.97/3.12  Parsing              : 0.35
% 8.97/3.12  CNF conversion       : 0.07
% 8.97/3.12  Main loop            : 1.54
% 8.97/3.12  Inferencing          : 0.55
% 8.97/3.12  Reduction            : 0.47
% 8.97/3.12  Demodulation         : 0.34
% 8.97/3.12  BG Simplification    : 0.07
% 8.97/3.12  Subsumption          : 0.37
% 8.97/3.12  Abstraction          : 0.08
% 8.97/3.12  MUC search           : 0.00
% 8.97/3.12  Cooper               : 0.00
% 8.97/3.12  Total                : 2.32
% 8.97/3.12  Index Insertion      : 0.00
% 8.97/3.12  Index Deletion       : 0.00
% 8.97/3.12  Index Matching       : 0.00
% 8.97/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
