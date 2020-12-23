%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:09 EST 2020

% Result     : Theorem 12.74s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :  173 (9123 expanded)
%              Number of leaves         :   39 (3740 expanded)
%              Depth                    :   28
%              Number of atoms          :  917 (70181 expanded)
%              Number of equality atoms :   34 (4726 expanded)
%              Maximal formula depth    :   24 (   7 average)
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

tff(f_303,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_198,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_228,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_176,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_264,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_108,plain,(
    ! [D_148,B_149,F_152,C_150,A_151] :
      ( r1_funct_2(A_151,B_149,C_150,D_148,F_152,F_152)
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(C_150,D_148)))
      | ~ v1_funct_2(F_152,C_150,D_148)
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(F_152,A_151,B_149)
      | ~ v1_funct_1(F_152)
      | v1_xboole_0(D_148)
      | v1_xboole_0(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_110,plain,(
    ! [A_151,B_149] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2('#skF_5',A_151,B_149)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_149) ) ),
    inference(resolution,[status(thm)],[c_40,c_108])).

tff(c_113,plain,(
    ! [A_151,B_149] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2('#skF_5',A_151,B_149)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_110])).

tff(c_114,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_120,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_117])).

tff(c_123,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_123])).

tff(c_129,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_128,plain,(
    ! [A_151,B_149] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2('#skF_5',A_151,B_149)
      | v1_xboole_0(B_149) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_46,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_94,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_pre_topc(k1_tsep_1(A_141,B_142,C_143),A_141)
      | ~ m1_pre_topc(C_143,A_141)
      | v2_struct_0(C_143)
      | ~ m1_pre_topc(B_142,A_141)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_97,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_94])).

tff(c_99,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_48,c_97])).

tff(c_100,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54,c_50,c_99])).

tff(c_187,plain,(
    ! [C_187,B_188,E_185,D_189,A_186] :
      ( k3_tmap_1(A_186,B_188,C_187,D_189,E_185) = k2_partfun1(u1_struct_0(C_187),u1_struct_0(B_188),E_185,u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,C_187)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187),u1_struct_0(B_188))))
      | ~ v1_funct_2(E_185,u1_struct_0(C_187),u1_struct_0(B_188))
      | ~ v1_funct_1(E_185)
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc(C_187,A_186)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_191,plain,(
    ! [A_186,D_189] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_40,c_187])).

tff(c_195,plain,(
    ! [A_186,D_189] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_42,c_191])).

tff(c_197,plain,(
    ! [A_190,D_191] :
      ( k3_tmap_1(A_190,'#skF_2','#skF_1',D_191,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,'#skF_1')
      | ~ m1_pre_topc(D_191,A_190)
      | ~ m1_pre_topc('#skF_1',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_195])).

tff(c_205,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_197])).

tff(c_217,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_52,c_205])).

tff(c_218,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_217])).

tff(c_147,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k2_partfun1(u1_struct_0(A_168),u1_struct_0(B_169),C_170,u1_struct_0(D_171)) = k2_tmap_1(A_168,B_169,C_170,D_171)
      | ~ m1_pre_topc(D_171,A_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_149,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_152,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_44,c_42,c_149])).

tff(c_153,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_152])).

tff(c_327,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_153])).

tff(c_334,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_327])).

tff(c_139,plain,(
    ! [C_162,D_161,B_163,A_165,E_164] :
      ( v1_funct_1(k3_tmap_1(A_165,B_163,C_162,D_161,E_164))
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162),u1_struct_0(B_163))))
      | ~ v1_funct_2(E_164,u1_struct_0(C_162),u1_struct_0(B_163))
      | ~ v1_funct_1(E_164)
      | ~ m1_pre_topc(D_161,A_165)
      | ~ m1_pre_topc(C_162,A_165)
      | ~ l1_pre_topc(B_163)
      | ~ v2_pre_topc(B_163)
      | v2_struct_0(B_163)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_141,plain,(
    ! [A_165,D_161] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_161,A_165)
      | ~ m1_pre_topc('#skF_1',A_165)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_40,c_139])).

tff(c_144,plain,(
    ! [A_165,D_161] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ m1_pre_topc(D_161,A_165)
      | ~ m1_pre_topc('#skF_1',A_165)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_42,c_141])).

tff(c_145,plain,(
    ! [A_165,D_161] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ m1_pre_topc(D_161,A_165)
      | ~ m1_pre_topc('#skF_1',A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_144])).

tff(c_348,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_145])).

tff(c_358,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_52,c_348])).

tff(c_359,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_358])).

tff(c_154,plain,(
    ! [D_172,A_176,B_174,C_173,E_175] :
      ( v1_funct_2(k3_tmap_1(A_176,B_174,C_173,D_172,E_175),u1_struct_0(D_172),u1_struct_0(B_174))
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_173),u1_struct_0(B_174))))
      | ~ v1_funct_2(E_175,u1_struct_0(C_173),u1_struct_0(B_174))
      | ~ v1_funct_1(E_175)
      | ~ m1_pre_topc(D_172,A_176)
      | ~ m1_pre_topc(C_173,A_176)
      | ~ l1_pre_topc(B_174)
      | ~ v2_pre_topc(B_174)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_156,plain,(
    ! [A_176,D_172] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_172,'#skF_5'),u1_struct_0(D_172),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_172,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_40,c_154])).

tff(c_159,plain,(
    ! [A_176,D_172] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_172,'#skF_5'),u1_struct_0(D_172),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_172,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_42,c_156])).

tff(c_160,plain,(
    ! [A_176,D_172] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_172,'#skF_5'),u1_struct_0(D_172),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_172,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_159])).

tff(c_345,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_160])).

tff(c_355,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_52,c_345])).

tff(c_356,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_355])).

tff(c_30,plain,(
    ! [E_72,C_70,B_69,D_71,A_68] :
      ( m1_subset_1(k3_tmap_1(A_68,B_69,C_70,D_71,E_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71),u1_struct_0(B_69))))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70),u1_struct_0(B_69))))
      | ~ v1_funct_2(E_72,u1_struct_0(C_70),u1_struct_0(B_69))
      | ~ v1_funct_1(E_72)
      | ~ m1_pre_topc(D_71,A_68)
      | ~ m1_pre_topc(C_70,A_68)
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_342,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_30])).

tff(c_352,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_100,c_52,c_44,c_42,c_40,c_342])).

tff(c_353,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_352])).

tff(c_203,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_197])).

tff(c_213,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_48,c_203])).

tff(c_214,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_213])).

tff(c_429,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_153])).

tff(c_436,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_429])).

tff(c_450,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_145])).

tff(c_460,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_48,c_450])).

tff(c_461,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_460])).

tff(c_447,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_160])).

tff(c_457,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100,c_48,c_447])).

tff(c_458,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_457])).

tff(c_444,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_30])).

tff(c_454,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_100,c_48,c_44,c_42,c_40,c_444])).

tff(c_455,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_454])).

tff(c_527,plain,(
    ! [C_204,D_208,A_205,E_209,F_207,B_206] :
      ( m1_subset_1(k10_tmap_1(A_205,B_206,C_204,D_208,E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_205,C_204,D_208)),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_208),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0(D_208),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0(C_204),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ m1_pre_topc(D_208,A_205)
      | v2_struct_0(D_208)
      | ~ m1_pre_topc(C_204,A_205)
      | v2_struct_0(C_204)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_544,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_527])).

tff(c_553,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_48,c_544])).

tff(c_554,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54,c_50,c_553])).

tff(c_403,plain,(
    ! [B_200,C_198,F_201,E_203,D_202,A_199] :
      ( v1_funct_2(k10_tmap_1(A_199,B_200,C_198,D_202,E_203,F_201),u1_struct_0(k1_tsep_1(A_199,C_198,D_202)),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_202),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0(D_202),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_198),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0(C_198),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | ~ m1_pre_topc(D_202,A_199)
      | v2_struct_0(D_202)
      | ~ m1_pre_topc(C_198,A_199)
      | v2_struct_0(C_198)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_406,plain,(
    ! [B_200,E_203,F_201] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_203,F_201),u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_403])).

tff(c_408,plain,(
    ! [B_200,E_203,F_201] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_203,F_201),u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_48,c_406])).

tff(c_1380,plain,(
    ! [B_265,E_266,F_267] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_265,'#skF_3','#skF_4',E_266,F_267),u1_struct_0('#skF_1'),u1_struct_0(B_265))
      | ~ m1_subset_1(F_267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_265))))
      | ~ v1_funct_2(F_267,u1_struct_0('#skF_4'),u1_struct_0(B_265))
      | ~ v1_funct_1(F_267)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_265))))
      | ~ v1_funct_2(E_266,u1_struct_0('#skF_3'),u1_struct_0(B_265))
      | ~ v1_funct_1(E_266)
      | ~ l1_pre_topc(B_265)
      | ~ v2_pre_topc(B_265)
      | v2_struct_0(B_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54,c_50,c_408])).

tff(c_1388,plain,(
    ! [E_266] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_266,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_266,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_266)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_455,c_1380])).

tff(c_1406,plain,(
    ! [E_266] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_266,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_266,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_266)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_461,c_458,c_1388])).

tff(c_1407,plain,(
    ! [E_266] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_266,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_266,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1406])).

tff(c_22,plain,(
    ! [F_64,D_62,A_59,C_61,E_63,B_60] :
      ( v1_funct_1(k10_tmap_1(A_59,B_60,C_61,D_62,E_63,F_64))
      | ~ m1_subset_1(F_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62),u1_struct_0(B_60))))
      | ~ v1_funct_2(F_64,u1_struct_0(D_62),u1_struct_0(B_60))
      | ~ v1_funct_1(F_64)
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0(B_60))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0(B_60))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc(D_62,A_59)
      | v2_struct_0(D_62)
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | ~ l1_pre_topc(B_60)
      | ~ v2_pre_topc(B_60)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_465,plain,(
    ! [A_59,C_61,E_63] :
      ( v1_funct_1(k10_tmap_1(A_59,'#skF_2',C_61,'#skF_4',E_63,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc('#skF_4',A_59)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_455,c_22])).

tff(c_480,plain,(
    ! [A_59,C_61,E_63] :
      ( v1_funct_1(k10_tmap_1(A_59,'#skF_2',C_61,'#skF_4',E_63,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc('#skF_4',A_59)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_461,c_458,c_465])).

tff(c_1284,plain,(
    ! [A_256,C_257,E_258] :
      ( v1_funct_1(k10_tmap_1(A_256,'#skF_2',C_257,'#skF_4',E_258,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_258,u1_struct_0(C_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_258)
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ m1_pre_topc(C_257,A_256)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_50,c_480])).

tff(c_1309,plain,(
    ! [A_256] :
      ( v1_funct_1(k10_tmap_1(A_256,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_353,c_1284])).

tff(c_1354,plain,(
    ! [A_256] :
      ( v1_funct_1(k10_tmap_1(A_256,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_356,c_1309])).

tff(c_1355,plain,(
    ! [A_256] :
      ( v1_funct_1(k10_tmap_1(A_256,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1354])).

tff(c_1562,plain,(
    ! [B_277,E_278,F_279] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_277,'#skF_3','#skF_4',E_278,F_279),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_277))))
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_277))))
      | ~ v1_funct_2(F_279,u1_struct_0('#skF_4'),u1_struct_0(B_277))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_278,u1_struct_0('#skF_3'),u1_struct_0(B_277))
      | ~ v1_funct_1(E_278)
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54,c_50,c_553])).

tff(c_256,plain,(
    ! [E_197,B_194,D_196,F_195,A_193,C_192] :
      ( v1_funct_1(k10_tmap_1(A_193,B_194,C_192,D_196,E_197,F_195))
      | ~ m1_subset_1(F_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_196),u1_struct_0(B_194))))
      | ~ v1_funct_2(F_195,u1_struct_0(D_196),u1_struct_0(B_194))
      | ~ v1_funct_1(F_195)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0(B_194))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0(B_194))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc(D_196,A_193)
      | v2_struct_0(D_196)
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc(B_194)
      | ~ v2_pre_topc(B_194)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_260,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_40,c_256])).

tff(c_264,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_42,c_260])).

tff(c_265,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_264])).

tff(c_1568,plain,(
    ! [A_193,E_278,F_279] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279))
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_279,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_278,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_278)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1562,c_265])).

tff(c_1589,plain,(
    ! [A_193,E_278,F_279] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_278,F_279))
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_279,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_278,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_278)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1568])).

tff(c_7379,plain,(
    ! [A_694,E_695,F_696] :
      ( v1_funct_1(k10_tmap_1(A_694,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_695,F_696),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_695,F_696),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_695,F_696))
      | ~ m1_pre_topc('#skF_1',A_694)
      | ~ l1_pre_topc(A_694)
      | ~ v2_pre_topc(A_694)
      | v2_struct_0(A_694)
      | ~ m1_subset_1(F_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_696,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_696)
      | ~ m1_subset_1(E_695,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_695,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_1589])).

tff(c_7381,plain,(
    ! [A_694,E_266] :
      ( v1_funct_1(k10_tmap_1(A_694,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_266,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_266,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_694)
      | ~ l1_pre_topc(A_694)
      | ~ v2_pre_topc(A_694)
      | v2_struct_0(A_694)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_266,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_1407,c_7379])).

tff(c_7458,plain,(
    ! [A_708,E_709] :
      ( v1_funct_1(k10_tmap_1(A_708,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_709,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_709,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708)
      | ~ m1_subset_1(E_709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_709,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_709) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_458,c_455,c_7381])).

tff(c_7464,plain,(
    ! [A_708] :
      ( v1_funct_1(k10_tmap_1(A_708,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_353,c_7458])).

tff(c_7474,plain,(
    ! [A_708] :
      ( v1_funct_1(k10_tmap_1(A_708,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_356,c_7464])).

tff(c_7479,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7474])).

tff(c_7482,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1355,c_7479])).

tff(c_7485,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_48,c_7482])).

tff(c_7487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7485])).

tff(c_7489,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7474])).

tff(c_582,plain,(
    ! [B_226,E_223,C_224,D_225,A_227] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226),E_223,k10_tmap_1(A_227,B_226,C_224,D_225,k3_tmap_1(A_227,B_226,k1_tsep_1(A_227,C_224,D_225),C_224,E_223),k3_tmap_1(A_227,B_226,k1_tsep_1(A_227,C_224,D_225),D_225,E_223)))
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226))))
      | ~ v1_funct_2(E_223,u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_225,A_227)
      | v2_struct_0(D_225)
      | ~ m1_pre_topc(C_224,A_227)
      | v2_struct_0(C_224)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

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

tff(c_5542,plain,(
    ! [C_626,B_624,A_627,D_625,E_623] :
      ( k10_tmap_1(A_627,B_624,C_626,D_625,k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),C_626,E_623),k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),D_625,E_623)) = E_623
      | ~ m1_subset_1(k10_tmap_1(A_627,B_624,C_626,D_625,k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),C_626,E_623),k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),D_625,E_623)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_627,C_626,D_625)),u1_struct_0(B_624))))
      | ~ v1_funct_2(k10_tmap_1(A_627,B_624,C_626,D_625,k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),C_626,E_623),k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),D_625,E_623)),u1_struct_0(k1_tsep_1(A_627,C_626,D_625)),u1_struct_0(B_624))
      | ~ v1_funct_1(k10_tmap_1(A_627,B_624,C_626,D_625,k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),C_626,E_623),k3_tmap_1(A_627,B_624,k1_tsep_1(A_627,C_626,D_625),D_625,E_623)))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_627,C_626,D_625)),u1_struct_0(B_624))))
      | ~ v1_funct_2(E_623,u1_struct_0(k1_tsep_1(A_627,C_626,D_625)),u1_struct_0(B_624))
      | ~ v1_funct_1(E_623)
      | ~ m1_pre_topc(D_625,A_627)
      | v2_struct_0(D_625)
      | ~ m1_pre_topc(C_626,A_627)
      | v2_struct_0(C_626)
      | ~ l1_pre_topc(B_624)
      | ~ v2_pre_topc(B_624)
      | v2_struct_0(B_624)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_582,c_4])).

tff(c_5560,plain,(
    ! [B_624,E_623] :
      ( k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_623),k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_623)) = E_623
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_623),k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_4',E_623)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_624))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_623),k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_623)),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_624))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_623),k3_tmap_1('#skF_1',B_624,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_623)))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_624))))
      | ~ v1_funct_2(E_623,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_624))
      | ~ v1_funct_1(E_623)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_624)
      | ~ v2_pre_topc(B_624)
      | v2_struct_0(B_624)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5542])).

tff(c_5569,plain,(
    ! [B_624,E_623] :
      ( k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_3',E_623),k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_4',E_623)) = E_623
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_3',E_623),k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_4',E_623)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_624))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_3',E_623),k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_4',E_623)),u1_struct_0('#skF_1'),u1_struct_0(B_624))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_624,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_3',E_623),k3_tmap_1('#skF_1',B_624,'#skF_1','#skF_4',E_623)))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_624))))
      | ~ v1_funct_2(E_623,u1_struct_0('#skF_1'),u1_struct_0(B_624))
      | ~ v1_funct_1(E_623)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_624)
      | ~ v2_pre_topc(B_624)
      | v2_struct_0(B_624)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_48,c_46,c_46,c_46,c_46,c_46,c_46,c_46,c_46,c_46,c_46,c_46,c_5560])).

tff(c_9778,plain,(
    ! [B_904,E_905] :
      ( k10_tmap_1('#skF_1',B_904,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_3',E_905),k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_4',E_905)) = E_905
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_904,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_3',E_905),k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_4',E_905)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_904))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_904,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_3',E_905),k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_4',E_905)),u1_struct_0('#skF_1'),u1_struct_0(B_904))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_904,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_3',E_905),k3_tmap_1('#skF_1',B_904,'#skF_1','#skF_4',E_905)))
      | ~ m1_subset_1(E_905,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_904))))
      | ~ v1_funct_2(E_905,u1_struct_0('#skF_1'),u1_struct_0(B_904))
      | ~ v1_funct_1(E_905)
      | ~ l1_pre_topc(B_904)
      | ~ v2_pre_topc(B_904)
      | v2_struct_0(B_904) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54,c_50,c_5569])).

tff(c_9817,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_9778])).

tff(c_9847,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_42,c_40,c_7489,c_334,c_436,c_334,c_436,c_334,c_334,c_436,c_9817])).

tff(c_9848,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_9847])).

tff(c_9852,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9848])).

tff(c_9855,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1407,c_9852])).

tff(c_9859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_356,c_353,c_9855])).

tff(c_9860,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9848])).

tff(c_9990,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_9860])).

tff(c_9993,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_554,c_9990])).

tff(c_9996,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_359,c_356,c_353,c_461,c_458,c_455,c_9993])).

tff(c_9998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_9996])).

tff(c_9999,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9860])).

tff(c_38,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_67,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_10009,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9999,c_67])).

tff(c_10133,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_128,c_10009])).

tff(c_10136,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_10133])).

tff(c_10138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_10136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.74/5.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.12  
% 12.79/5.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.84/5.13  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.84/5.13  
% 12.84/5.13  %Foreground sorts:
% 12.84/5.13  
% 12.84/5.13  
% 12.84/5.13  %Background operators:
% 12.84/5.13  
% 12.84/5.13  
% 12.84/5.13  %Foreground operators:
% 12.84/5.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.84/5.13  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.84/5.13  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 12.84/5.13  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.84/5.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.84/5.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.84/5.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.84/5.13  tff('#skF_5', type, '#skF_5': $i).
% 12.84/5.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.84/5.13  tff('#skF_2', type, '#skF_2': $i).
% 12.84/5.13  tff('#skF_3', type, '#skF_3': $i).
% 12.84/5.13  tff('#skF_1', type, '#skF_1': $i).
% 12.84/5.13  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.84/5.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.84/5.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.84/5.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.84/5.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.84/5.13  tff('#skF_4', type, '#skF_4': $i).
% 12.84/5.13  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 12.84/5.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.84/5.13  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.84/5.13  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.84/5.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.84/5.13  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.84/5.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.84/5.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.84/5.13  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 12.84/5.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.84/5.13  
% 12.84/5.16  tff(f_303, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_tmap_1)).
% 12.84/5.16  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.84/5.16  tff(f_75, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 12.84/5.16  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 12.84/5.16  tff(f_198, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 12.84/5.16  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 12.84/5.16  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 12.84/5.16  tff(f_228, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 12.84/5.16  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 12.84/5.16  tff(f_264, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 12.84/5.16  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 12.84/5.16  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.84/5.16  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_108, plain, (![D_148, B_149, F_152, C_150, A_151]: (r1_funct_2(A_151, B_149, C_150, D_148, F_152, F_152) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(C_150, D_148))) | ~v1_funct_2(F_152, C_150, D_148) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(F_152, A_151, B_149) | ~v1_funct_1(F_152) | v1_xboole_0(D_148) | v1_xboole_0(B_149))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.84/5.16  tff(c_110, plain, (![A_151, B_149]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2('#skF_5', A_151, B_149) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_149))), inference(resolution, [status(thm)], [c_40, c_108])).
% 12.84/5.16  tff(c_113, plain, (![A_151, B_149]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2('#skF_5', A_151, B_149) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_110])).
% 12.84/5.16  tff(c_114, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_113])).
% 12.84/5.16  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.84/5.16  tff(c_117, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_114, c_8])).
% 12.84/5.16  tff(c_120, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_117])).
% 12.84/5.16  tff(c_123, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_120])).
% 12.84/5.16  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_123])).
% 12.84/5.16  tff(c_129, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_113])).
% 12.84/5.16  tff(c_128, plain, (![A_151, B_149]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2('#skF_5', A_151, B_149) | v1_xboole_0(B_149))), inference(splitRight, [status(thm)], [c_113])).
% 12.84/5.16  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_46, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_94, plain, (![A_141, B_142, C_143]: (m1_pre_topc(k1_tsep_1(A_141, B_142, C_143), A_141) | ~m1_pre_topc(C_143, A_141) | v2_struct_0(C_143) | ~m1_pre_topc(B_142, A_141) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_198])).
% 12.84/5.16  tff(c_97, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_94])).
% 12.84/5.16  tff(c_99, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_48, c_97])).
% 12.84/5.16  tff(c_100, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_54, c_50, c_99])).
% 12.84/5.16  tff(c_187, plain, (![C_187, B_188, E_185, D_189, A_186]: (k3_tmap_1(A_186, B_188, C_187, D_189, E_185)=k2_partfun1(u1_struct_0(C_187), u1_struct_0(B_188), E_185, u1_struct_0(D_189)) | ~m1_pre_topc(D_189, C_187) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187), u1_struct_0(B_188)))) | ~v1_funct_2(E_185, u1_struct_0(C_187), u1_struct_0(B_188)) | ~v1_funct_1(E_185) | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc(C_187, A_186) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.84/5.16  tff(c_191, plain, (![A_186, D_189]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc('#skF_1', A_186) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_40, c_187])).
% 12.84/5.16  tff(c_195, plain, (![A_186, D_189]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc('#skF_1', A_186) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_42, c_191])).
% 12.84/5.16  tff(c_197, plain, (![A_190, D_191]: (k3_tmap_1(A_190, '#skF_2', '#skF_1', D_191, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_191)) | ~m1_pre_topc(D_191, '#skF_1') | ~m1_pre_topc(D_191, A_190) | ~m1_pre_topc('#skF_1', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(negUnitSimplification, [status(thm)], [c_60, c_195])).
% 12.84/5.16  tff(c_205, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_197])).
% 12.84/5.16  tff(c_217, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_52, c_205])).
% 12.84/5.16  tff(c_218, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_217])).
% 12.84/5.16  tff(c_147, plain, (![A_168, B_169, C_170, D_171]: (k2_partfun1(u1_struct_0(A_168), u1_struct_0(B_169), C_170, u1_struct_0(D_171))=k2_tmap_1(A_168, B_169, C_170, D_171) | ~m1_pre_topc(D_171, A_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.84/5.16  tff(c_149, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_147])).
% 12.84/5.16  tff(c_152, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_44, c_42, c_149])).
% 12.84/5.16  tff(c_153, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_152])).
% 12.84/5.16  tff(c_327, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_218, c_153])).
% 12.84/5.16  tff(c_334, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_327])).
% 12.84/5.16  tff(c_139, plain, (![C_162, D_161, B_163, A_165, E_164]: (v1_funct_1(k3_tmap_1(A_165, B_163, C_162, D_161, E_164)) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162), u1_struct_0(B_163)))) | ~v1_funct_2(E_164, u1_struct_0(C_162), u1_struct_0(B_163)) | ~v1_funct_1(E_164) | ~m1_pre_topc(D_161, A_165) | ~m1_pre_topc(C_162, A_165) | ~l1_pre_topc(B_163) | ~v2_pre_topc(B_163) | v2_struct_0(B_163) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_228])).
% 12.84/5.16  tff(c_141, plain, (![A_165, D_161]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_161, A_165) | ~m1_pre_topc('#skF_1', A_165) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_40, c_139])).
% 12.84/5.16  tff(c_144, plain, (![A_165, D_161]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~m1_pre_topc(D_161, A_165) | ~m1_pre_topc('#skF_1', A_165) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_42, c_141])).
% 12.84/5.16  tff(c_145, plain, (![A_165, D_161]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~m1_pre_topc(D_161, A_165) | ~m1_pre_topc('#skF_1', A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_60, c_144])).
% 12.84/5.16  tff(c_348, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_334, c_145])).
% 12.84/5.16  tff(c_358, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_52, c_348])).
% 12.84/5.16  tff(c_359, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_358])).
% 12.84/5.16  tff(c_154, plain, (![D_172, A_176, B_174, C_173, E_175]: (v1_funct_2(k3_tmap_1(A_176, B_174, C_173, D_172, E_175), u1_struct_0(D_172), u1_struct_0(B_174)) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_173), u1_struct_0(B_174)))) | ~v1_funct_2(E_175, u1_struct_0(C_173), u1_struct_0(B_174)) | ~v1_funct_1(E_175) | ~m1_pre_topc(D_172, A_176) | ~m1_pre_topc(C_173, A_176) | ~l1_pre_topc(B_174) | ~v2_pre_topc(B_174) | v2_struct_0(B_174) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_228])).
% 12.84/5.16  tff(c_156, plain, (![A_176, D_172]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_172, '#skF_5'), u1_struct_0(D_172), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_172, A_176) | ~m1_pre_topc('#skF_1', A_176) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_40, c_154])).
% 12.84/5.16  tff(c_159, plain, (![A_176, D_172]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_172, '#skF_5'), u1_struct_0(D_172), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_172, A_176) | ~m1_pre_topc('#skF_1', A_176) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_42, c_156])).
% 12.84/5.16  tff(c_160, plain, (![A_176, D_172]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_172, '#skF_5'), u1_struct_0(D_172), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_172, A_176) | ~m1_pre_topc('#skF_1', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_60, c_159])).
% 12.84/5.16  tff(c_345, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_334, c_160])).
% 12.84/5.16  tff(c_355, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_52, c_345])).
% 12.84/5.16  tff(c_356, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_355])).
% 12.84/5.16  tff(c_30, plain, (![E_72, C_70, B_69, D_71, A_68]: (m1_subset_1(k3_tmap_1(A_68, B_69, C_70, D_71, E_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71), u1_struct_0(B_69)))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70), u1_struct_0(B_69)))) | ~v1_funct_2(E_72, u1_struct_0(C_70), u1_struct_0(B_69)) | ~v1_funct_1(E_72) | ~m1_pre_topc(D_71, A_68) | ~m1_pre_topc(C_70, A_68) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_228])).
% 12.84/5.16  tff(c_342, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_334, c_30])).
% 12.84/5.16  tff(c_352, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_100, c_52, c_44, c_42, c_40, c_342])).
% 12.84/5.16  tff(c_353, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_352])).
% 12.84/5.16  tff(c_203, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_197])).
% 12.84/5.16  tff(c_213, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_48, c_203])).
% 12.84/5.16  tff(c_214, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_213])).
% 12.84/5.16  tff(c_429, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_214, c_153])).
% 12.84/5.16  tff(c_436, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_429])).
% 12.84/5.16  tff(c_450, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_436, c_145])).
% 12.84/5.16  tff(c_460, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_48, c_450])).
% 12.84/5.16  tff(c_461, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_460])).
% 12.84/5.16  tff(c_447, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_436, c_160])).
% 12.84/5.16  tff(c_457, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100, c_48, c_447])).
% 12.84/5.16  tff(c_458, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_457])).
% 12.84/5.16  tff(c_444, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_436, c_30])).
% 12.84/5.16  tff(c_454, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_100, c_48, c_44, c_42, c_40, c_444])).
% 12.84/5.16  tff(c_455, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_454])).
% 12.84/5.16  tff(c_527, plain, (![C_204, D_208, A_205, E_209, F_207, B_206]: (m1_subset_1(k10_tmap_1(A_205, B_206, C_204, D_208, E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_205, C_204, D_208)), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_208), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0(D_208), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0(C_204), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~m1_pre_topc(D_208, A_205) | v2_struct_0(D_208) | ~m1_pre_topc(C_204, A_205) | v2_struct_0(C_204) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.84/5.16  tff(c_544, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_527])).
% 12.84/5.16  tff(c_553, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_48, c_544])).
% 12.84/5.16  tff(c_554, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206))), inference(negUnitSimplification, [status(thm)], [c_66, c_54, c_50, c_553])).
% 12.84/5.16  tff(c_403, plain, (![B_200, C_198, F_201, E_203, D_202, A_199]: (v1_funct_2(k10_tmap_1(A_199, B_200, C_198, D_202, E_203, F_201), u1_struct_0(k1_tsep_1(A_199, C_198, D_202)), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_202), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0(D_202), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_198), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0(C_198), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | ~m1_pre_topc(D_202, A_199) | v2_struct_0(D_202) | ~m1_pre_topc(C_198, A_199) | v2_struct_0(C_198) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.84/5.16  tff(c_406, plain, (![B_200, E_203, F_201]: (v1_funct_2(k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_203, F_201), u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_403])).
% 12.84/5.16  tff(c_408, plain, (![B_200, E_203, F_201]: (v1_funct_2(k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_203, F_201), u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_48, c_406])).
% 12.84/5.16  tff(c_1380, plain, (![B_265, E_266, F_267]: (v1_funct_2(k10_tmap_1('#skF_1', B_265, '#skF_3', '#skF_4', E_266, F_267), u1_struct_0('#skF_1'), u1_struct_0(B_265)) | ~m1_subset_1(F_267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_265)))) | ~v1_funct_2(F_267, u1_struct_0('#skF_4'), u1_struct_0(B_265)) | ~v1_funct_1(F_267) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_265)))) | ~v1_funct_2(E_266, u1_struct_0('#skF_3'), u1_struct_0(B_265)) | ~v1_funct_1(E_266) | ~l1_pre_topc(B_265) | ~v2_pre_topc(B_265) | v2_struct_0(B_265))), inference(negUnitSimplification, [status(thm)], [c_66, c_54, c_50, c_408])).
% 12.84/5.16  tff(c_1388, plain, (![E_266]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_266, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_266, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_266) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_455, c_1380])).
% 12.84/5.16  tff(c_1406, plain, (![E_266]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_266, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_266, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_266) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_461, c_458, c_1388])).
% 12.84/5.16  tff(c_1407, plain, (![E_266]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_266, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_266, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_266))), inference(negUnitSimplification, [status(thm)], [c_60, c_1406])).
% 12.84/5.16  tff(c_22, plain, (![F_64, D_62, A_59, C_61, E_63, B_60]: (v1_funct_1(k10_tmap_1(A_59, B_60, C_61, D_62, E_63, F_64)) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62), u1_struct_0(B_60)))) | ~v1_funct_2(F_64, u1_struct_0(D_62), u1_struct_0(B_60)) | ~v1_funct_1(F_64) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_60)))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0(B_60)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_62, A_59) | v2_struct_0(D_62) | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.84/5.16  tff(c_465, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_455, c_22])).
% 12.84/5.16  tff(c_480, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_461, c_458, c_465])).
% 12.84/5.16  tff(c_1284, plain, (![A_256, C_257, E_258]: (v1_funct_1(k10_tmap_1(A_256, '#skF_2', C_257, '#skF_4', E_258, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_258, u1_struct_0(C_257), u1_struct_0('#skF_2')) | ~v1_funct_1(E_258) | ~m1_pre_topc('#skF_4', A_256) | ~m1_pre_topc(C_257, A_256) | v2_struct_0(C_257) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(negUnitSimplification, [status(thm)], [c_60, c_50, c_480])).
% 12.84/5.16  tff(c_1309, plain, (![A_256]: (v1_funct_1(k10_tmap_1(A_256, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', A_256) | ~m1_pre_topc('#skF_3', A_256) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_353, c_1284])).
% 12.84/5.16  tff(c_1354, plain, (![A_256]: (v1_funct_1(k10_tmap_1(A_256, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_256) | ~m1_pre_topc('#skF_3', A_256) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_356, c_1309])).
% 12.84/5.16  tff(c_1355, plain, (![A_256]: (v1_funct_1(k10_tmap_1(A_256, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_256) | ~m1_pre_topc('#skF_3', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(negUnitSimplification, [status(thm)], [c_54, c_1354])).
% 12.84/5.16  tff(c_1562, plain, (![B_277, E_278, F_279]: (m1_subset_1(k10_tmap_1('#skF_1', B_277, '#skF_3', '#skF_4', E_278, F_279), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_277)))) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_277)))) | ~v1_funct_2(F_279, u1_struct_0('#skF_4'), u1_struct_0(B_277)) | ~v1_funct_1(F_279) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_277)))) | ~v1_funct_2(E_278, u1_struct_0('#skF_3'), u1_struct_0(B_277)) | ~v1_funct_1(E_278) | ~l1_pre_topc(B_277) | ~v2_pre_topc(B_277) | v2_struct_0(B_277))), inference(negUnitSimplification, [status(thm)], [c_66, c_54, c_50, c_553])).
% 12.84/5.16  tff(c_256, plain, (![E_197, B_194, D_196, F_195, A_193, C_192]: (v1_funct_1(k10_tmap_1(A_193, B_194, C_192, D_196, E_197, F_195)) | ~m1_subset_1(F_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_196), u1_struct_0(B_194)))) | ~v1_funct_2(F_195, u1_struct_0(D_196), u1_struct_0(B_194)) | ~v1_funct_1(F_195) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0(B_194)))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0(B_194)) | ~v1_funct_1(E_197) | ~m1_pre_topc(D_196, A_193) | v2_struct_0(D_196) | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc(B_194) | ~v2_pre_topc(B_194) | v2_struct_0(B_194) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.84/5.16  tff(c_260, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_40, c_256])).
% 12.84/5.16  tff(c_264, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_42, c_260])).
% 12.84/5.16  tff(c_265, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_264])).
% 12.84/5.16  tff(c_1568, plain, (![A_193, E_278, F_279]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279)) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_279, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_279) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_278, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_278) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1562, c_265])).
% 12.84/5.16  tff(c_1589, plain, (![A_193, E_278, F_279]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_278, F_279)) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_279, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_279) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_278, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_278) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1568])).
% 12.84/5.16  tff(c_7379, plain, (![A_694, E_695, F_696]: (v1_funct_1(k10_tmap_1(A_694, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_695, F_696), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_695, F_696), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_695, F_696)) | ~m1_pre_topc('#skF_1', A_694) | ~l1_pre_topc(A_694) | ~v2_pre_topc(A_694) | v2_struct_0(A_694) | ~m1_subset_1(F_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_696, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_696) | ~m1_subset_1(E_695, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_695, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_695))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_1589])).
% 12.84/5.16  tff(c_7381, plain, (![A_694, E_266]: (v1_funct_1(k10_tmap_1(A_694, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_266, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_266, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_694) | ~l1_pre_topc(A_694) | ~v2_pre_topc(A_694) | v2_struct_0(A_694) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_266, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_1407, c_7379])).
% 12.84/5.16  tff(c_7458, plain, (![A_708, E_709]: (v1_funct_1(k10_tmap_1(A_708, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_709, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_709, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_708) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708) | ~m1_subset_1(E_709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_709, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_709))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_458, c_455, c_7381])).
% 12.84/5.16  tff(c_7464, plain, (![A_708]: (v1_funct_1(k10_tmap_1(A_708, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_708) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_353, c_7458])).
% 12.84/5.16  tff(c_7474, plain, (![A_708]: (v1_funct_1(k10_tmap_1(A_708, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_708) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_356, c_7464])).
% 12.84/5.16  tff(c_7479, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_7474])).
% 12.84/5.16  tff(c_7482, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1355, c_7479])).
% 12.84/5.16  tff(c_7485, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_48, c_7482])).
% 12.84/5.16  tff(c_7487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_7485])).
% 12.84/5.16  tff(c_7489, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_7474])).
% 12.84/5.16  tff(c_582, plain, (![B_226, E_223, C_224, D_225, A_227]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226), E_223, k10_tmap_1(A_227, B_226, C_224, D_225, k3_tmap_1(A_227, B_226, k1_tsep_1(A_227, C_224, D_225), C_224, E_223), k3_tmap_1(A_227, B_226, k1_tsep_1(A_227, C_224, D_225), D_225, E_223))) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226)))) | ~v1_funct_2(E_223, u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226)) | ~v1_funct_1(E_223) | ~m1_pre_topc(D_225, A_227) | v2_struct_0(D_225) | ~m1_pre_topc(C_224, A_227) | v2_struct_0(C_224) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_264])).
% 12.84/5.16  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.84/5.16  tff(c_5542, plain, (![C_626, B_624, A_627, D_625, E_623]: (k10_tmap_1(A_627, B_624, C_626, D_625, k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), C_626, E_623), k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), D_625, E_623))=E_623 | ~m1_subset_1(k10_tmap_1(A_627, B_624, C_626, D_625, k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), C_626, E_623), k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), D_625, E_623)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_627, C_626, D_625)), u1_struct_0(B_624)))) | ~v1_funct_2(k10_tmap_1(A_627, B_624, C_626, D_625, k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), C_626, E_623), k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), D_625, E_623)), u1_struct_0(k1_tsep_1(A_627, C_626, D_625)), u1_struct_0(B_624)) | ~v1_funct_1(k10_tmap_1(A_627, B_624, C_626, D_625, k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), C_626, E_623), k3_tmap_1(A_627, B_624, k1_tsep_1(A_627, C_626, D_625), D_625, E_623))) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_627, C_626, D_625)), u1_struct_0(B_624)))) | ~v1_funct_2(E_623, u1_struct_0(k1_tsep_1(A_627, C_626, D_625)), u1_struct_0(B_624)) | ~v1_funct_1(E_623) | ~m1_pre_topc(D_625, A_627) | v2_struct_0(D_625) | ~m1_pre_topc(C_626, A_627) | v2_struct_0(C_626) | ~l1_pre_topc(B_624) | ~v2_pre_topc(B_624) | v2_struct_0(B_624) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(resolution, [status(thm)], [c_582, c_4])).
% 12.84/5.16  tff(c_5560, plain, (![B_624, E_623]: (k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_623))=E_623 | ~m1_subset_1(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_4', E_623)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_624)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_623)), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_624)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_623))) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_624)))) | ~v1_funct_2(E_623, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_624)) | ~v1_funct_1(E_623) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_624) | ~v2_pre_topc(B_624) | v2_struct_0(B_624) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_5542])).
% 12.84/5.16  tff(c_5569, plain, (![B_624, E_623]: (k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_4', E_623))=E_623 | ~m1_subset_1(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_4', E_623)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_624)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_4', E_623)), u1_struct_0('#skF_1'), u1_struct_0(B_624)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_624, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_3', E_623), k3_tmap_1('#skF_1', B_624, '#skF_1', '#skF_4', E_623))) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_624)))) | ~v1_funct_2(E_623, u1_struct_0('#skF_1'), u1_struct_0(B_624)) | ~v1_funct_1(E_623) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_624) | ~v2_pre_topc(B_624) | v2_struct_0(B_624) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_48, c_46, c_46, c_46, c_46, c_46, c_46, c_46, c_46, c_46, c_46, c_46, c_5560])).
% 12.84/5.16  tff(c_9778, plain, (![B_904, E_905]: (k10_tmap_1('#skF_1', B_904, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_3', E_905), k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_4', E_905))=E_905 | ~m1_subset_1(k10_tmap_1('#skF_1', B_904, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_3', E_905), k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_4', E_905)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_904)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_904, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_3', E_905), k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_4', E_905)), u1_struct_0('#skF_1'), u1_struct_0(B_904)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_904, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_3', E_905), k3_tmap_1('#skF_1', B_904, '#skF_1', '#skF_4', E_905))) | ~m1_subset_1(E_905, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_904)))) | ~v1_funct_2(E_905, u1_struct_0('#skF_1'), u1_struct_0(B_904)) | ~v1_funct_1(E_905) | ~l1_pre_topc(B_904) | ~v2_pre_topc(B_904) | v2_struct_0(B_904))), inference(negUnitSimplification, [status(thm)], [c_66, c_54, c_50, c_5569])).
% 12.84/5.16  tff(c_9817, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_436, c_9778])).
% 12.84/5.16  tff(c_9847, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_42, c_40, c_7489, c_334, c_436, c_334, c_436, c_334, c_334, c_436, c_9817])).
% 12.84/5.16  tff(c_9848, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_9847])).
% 12.84/5.16  tff(c_9852, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_9848])).
% 12.84/5.16  tff(c_9855, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_1407, c_9852])).
% 12.84/5.16  tff(c_9859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_356, c_353, c_9855])).
% 12.84/5.16  tff(c_9860, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_9848])).
% 12.84/5.16  tff(c_9990, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_9860])).
% 12.84/5.16  tff(c_9993, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_554, c_9990])).
% 12.84/5.16  tff(c_9996, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_359, c_356, c_353, c_461, c_458, c_455, c_9993])).
% 12.84/5.16  tff(c_9998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_9996])).
% 12.84/5.16  tff(c_9999, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_9860])).
% 12.84/5.16  tff(c_38, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.84/5.16  tff(c_67, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38])).
% 12.84/5.16  tff(c_10009, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9999, c_67])).
% 12.84/5.16  tff(c_10133, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_128, c_10009])).
% 12.84/5.16  tff(c_10136, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_10133])).
% 12.84/5.16  tff(c_10138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_10136])).
% 12.84/5.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.84/5.16  
% 12.84/5.16  Inference rules
% 12.84/5.16  ----------------------
% 12.84/5.16  #Ref     : 0
% 12.84/5.16  #Sup     : 1861
% 12.84/5.16  #Fact    : 0
% 12.84/5.16  #Define  : 0
% 12.84/5.16  #Split   : 39
% 12.84/5.16  #Chain   : 0
% 12.84/5.16  #Close   : 0
% 12.84/5.16  
% 12.84/5.16  Ordering : KBO
% 12.84/5.16  
% 12.84/5.16  Simplification rules
% 12.84/5.16  ----------------------
% 12.84/5.16  #Subsume      : 1987
% 12.84/5.16  #Demod        : 5469
% 12.84/5.16  #Tautology    : 283
% 12.84/5.16  #SimpNegUnit  : 879
% 12.84/5.16  #BackRed      : 44
% 12.84/5.16  
% 12.84/5.16  #Partial instantiations: 0
% 12.84/5.16  #Strategies tried      : 1
% 12.84/5.16  
% 12.84/5.16  Timing (in seconds)
% 12.84/5.16  ----------------------
% 12.84/5.16  Preprocessing        : 0.40
% 12.84/5.16  Parsing              : 0.22
% 12.84/5.16  CNF conversion       : 0.04
% 12.84/5.16  Main loop            : 3.94
% 12.84/5.16  Inferencing          : 1.12
% 12.84/5.16  Reduction            : 1.44
% 12.84/5.16  Demodulation         : 1.15
% 12.84/5.16  BG Simplification    : 0.08
% 12.84/5.16  Subsumption          : 1.16
% 12.84/5.16  Abstraction          : 0.15
% 12.84/5.16  MUC search           : 0.00
% 12.84/5.16  Cooper               : 0.00
% 12.84/5.16  Total                : 4.40
% 12.84/5.16  Index Insertion      : 0.00
% 12.84/5.16  Index Deletion       : 0.00
% 12.84/5.16  Index Matching       : 0.00
% 12.84/5.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
