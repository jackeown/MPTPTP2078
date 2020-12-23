%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:09 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  253 (8976 expanded)
%              Number of leaves         :   39 (3503 expanded)
%              Depth                    :   36
%              Number of atoms          :  984 (68792 expanded)
%              Number of equality atoms :   32 (4644 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_280,negated_conjecture,(
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

tff(f_201,axiom,(
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

tff(f_241,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_237,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_96,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( v1_funct_1(k2_tmap_1(A_138,B_139,C_140,D_141))
      | ~ l1_struct_0(D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_140,u1_struct_0(A_138),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ l1_struct_0(B_139)
      | ~ l1_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_98,plain,(
    ! [D_141] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_141))
      | ~ l1_struct_0(D_141)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_101,plain,(
    ! [D_141] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_141))
      | ~ l1_struct_0(D_141)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_98])).

tff(c_102,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_112,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_112])).

tff(c_117,plain,(
    ! [D_141] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_141))
      | ~ l1_struct_0(D_141) ) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_122,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_122])).

tff(c_128,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_144,plain,(
    ! [C_160,D_158,B_156,F_159,A_157] :
      ( r1_funct_2(A_157,B_156,C_160,D_158,F_159,F_159)
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(C_160,D_158)))
      | ~ v1_funct_2(F_159,C_160,D_158)
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2(F_159,A_157,B_156)
      | ~ v1_funct_1(F_159)
      | v1_xboole_0(D_158)
      | v1_xboole_0(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_146,plain,(
    ! [A_157,B_156] :
      ( r1_funct_2(A_157,B_156,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2('#skF_5',A_157,B_156)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_156) ) ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_149,plain,(
    ! [A_157,B_156] :
      ( r1_funct_2(A_157,B_156,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2('#skF_5',A_157,B_156)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_146])).

tff(c_150,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_153,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_156,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_156])).

tff(c_160,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_159,plain,(
    ! [A_157,B_156] :
      ( r1_funct_2(A_157,B_156,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2('#skF_5',A_157,B_156)
      | v1_xboole_0(B_156) ) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_72,plain,(
    ! [B_132,A_133] :
      ( l1_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_88,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_81])).

tff(c_118,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_26,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( m1_subset_1(k2_tmap_1(A_68,B_69,C_70,D_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71),u1_struct_0(B_69))))
      | ~ l1_struct_0(D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_69))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ v1_funct_1(C_70)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_137,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( v1_funct_2(k2_tmap_1(A_151,B_152,C_153,D_154),u1_struct_0(D_154),u1_struct_0(B_152))
      | ~ l1_struct_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151),u1_struct_0(B_152))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_151),u1_struct_0(B_152))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0(B_152)
      | ~ l1_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_139,plain,(
    ! [D_154] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154),u1_struct_0(D_154),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_154)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_142,plain,(
    ! [D_154] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154),u1_struct_0(D_154),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_139])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_85,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_44,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_378,plain,(
    ! [A_200,E_198,C_199,F_202,D_203,B_201] :
      ( v1_funct_2(k10_tmap_1(A_200,B_201,C_199,D_203,E_198,F_202),u1_struct_0(k1_tsep_1(A_200,C_199,D_203)),u1_struct_0(B_201))
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_203),u1_struct_0(B_201))))
      | ~ v1_funct_2(F_202,u1_struct_0(D_203),u1_struct_0(B_201))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199),u1_struct_0(B_201))))
      | ~ v1_funct_2(E_198,u1_struct_0(C_199),u1_struct_0(B_201))
      | ~ v1_funct_1(E_198)
      | ~ m1_pre_topc(D_203,A_200)
      | v2_struct_0(D_203)
      | ~ m1_pre_topc(C_199,A_200)
      | v2_struct_0(C_199)
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_381,plain,(
    ! [B_201,E_198,F_202] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_201,'#skF_3','#skF_4',E_198,F_202),u1_struct_0('#skF_1'),u1_struct_0(B_201))
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_201))))
      | ~ v1_funct_2(F_202,u1_struct_0('#skF_4'),u1_struct_0(B_201))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_201))))
      | ~ v1_funct_2(E_198,u1_struct_0('#skF_3'),u1_struct_0(B_201))
      | ~ v1_funct_1(E_198)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_378])).

tff(c_383,plain,(
    ! [B_201,E_198,F_202] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_201,'#skF_3','#skF_4',E_198,F_202),u1_struct_0('#skF_1'),u1_struct_0(B_201))
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_201))))
      | ~ v1_funct_2(F_202,u1_struct_0('#skF_4'),u1_struct_0(B_201))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_201))))
      | ~ v1_funct_2(E_198,u1_struct_0('#skF_3'),u1_struct_0(B_201))
      | ~ v1_funct_1(E_198)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_381])).

tff(c_521,plain,(
    ! [B_216,E_217,F_218] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_216,'#skF_3','#skF_4',E_217,F_218),u1_struct_0('#skF_1'),u1_struct_0(B_216))
      | ~ m1_subset_1(F_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_216))))
      | ~ v1_funct_2(F_218,u1_struct_0('#skF_4'),u1_struct_0(B_216))
      | ~ v1_funct_1(F_218)
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_216))))
      | ~ v1_funct_2(E_217,u1_struct_0('#skF_3'),u1_struct_0(B_216))
      | ~ v1_funct_1(E_217)
      | ~ l1_pre_topc(B_216)
      | ~ v2_pre_topc(B_216)
      | v2_struct_0(B_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_383])).

tff(c_525,plain,(
    ! [B_69,E_217,A_68,C_70] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_69,'#skF_3','#skF_4',E_217,k2_tmap_1(A_68,B_69,C_70,'#skF_4')),u1_struct_0('#skF_1'),u1_struct_0(B_69))
      | ~ v1_funct_2(k2_tmap_1(A_68,B_69,C_70,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_69))
      | ~ v1_funct_1(k2_tmap_1(A_68,B_69,C_70,'#skF_4'))
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_69))))
      | ~ v1_funct_2(E_217,u1_struct_0('#skF_3'),u1_struct_0(B_69))
      | ~ v1_funct_1(E_217)
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_69))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ v1_funct_1(C_70)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_26,c_521])).

tff(c_2837,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_2840,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2837])).

tff(c_2844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2840])).

tff(c_2846,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_127,plain,(
    ! [D_141] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_141))
      | ~ l1_struct_0(D_141) ) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_2847,plain,(
    ! [B_516,E_517,A_518,C_519] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',E_517,k2_tmap_1(A_518,B_516,C_519,'#skF_4')),u1_struct_0('#skF_1'),u1_struct_0(B_516))
      | ~ v1_funct_2(k2_tmap_1(A_518,B_516,C_519,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_516))
      | ~ v1_funct_1(k2_tmap_1(A_518,B_516,C_519,'#skF_4'))
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_516))))
      | ~ v1_funct_2(E_517,u1_struct_0('#skF_3'),u1_struct_0(B_516))
      | ~ v1_funct_1(E_517)
      | ~ l1_pre_topc(B_516)
      | ~ v2_pre_topc(B_516)
      | v2_struct_0(B_516)
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_518),u1_struct_0(B_516))))
      | ~ v1_funct_2(C_519,u1_struct_0(A_518),u1_struct_0(B_516))
      | ~ v1_funct_1(C_519)
      | ~ l1_struct_0(B_516)
      | ~ l1_struct_0(A_518) ) ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_665,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_668,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_665])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_668])).

tff(c_674,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_278,plain,(
    ! [C_193,F_196,A_194,D_197,E_192,B_195] :
      ( v1_funct_1(k10_tmap_1(A_194,B_195,C_193,D_197,E_192,F_196))
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_197),u1_struct_0(B_195))))
      | ~ v1_funct_2(F_196,u1_struct_0(D_197),u1_struct_0(B_195))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193),u1_struct_0(B_195))))
      | ~ v1_funct_2(E_192,u1_struct_0(C_193),u1_struct_0(B_195))
      | ~ v1_funct_1(E_192)
      | ~ m1_pre_topc(D_197,A_194)
      | v2_struct_0(D_197)
      | ~ m1_pre_topc(C_193,A_194)
      | v2_struct_0(C_193)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1033,plain,(
    ! [C_342,B_341,D_339,A_344,C_340,A_338,E_343] :
      ( v1_funct_1(k10_tmap_1(A_338,B_341,C_342,D_339,E_343,k2_tmap_1(A_344,B_341,C_340,D_339)))
      | ~ v1_funct_2(k2_tmap_1(A_344,B_341,C_340,D_339),u1_struct_0(D_339),u1_struct_0(B_341))
      | ~ v1_funct_1(k2_tmap_1(A_344,B_341,C_340,D_339))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0(B_341))))
      | ~ v1_funct_2(E_343,u1_struct_0(C_342),u1_struct_0(B_341))
      | ~ v1_funct_1(E_343)
      | ~ m1_pre_topc(D_339,A_338)
      | v2_struct_0(D_339)
      | ~ m1_pre_topc(C_342,A_338)
      | v2_struct_0(C_342)
      | ~ l1_pre_topc(B_341)
      | ~ v2_pre_topc(B_341)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338)
      | ~ l1_struct_0(D_339)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344),u1_struct_0(B_341))))
      | ~ v1_funct_2(C_340,u1_struct_0(A_344),u1_struct_0(B_341))
      | ~ v1_funct_1(C_340)
      | ~ l1_struct_0(B_341)
      | ~ l1_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_26,c_278])).

tff(c_1043,plain,(
    ! [A_338,C_342,D_154,E_343] :
      ( v1_funct_1(k10_tmap_1(A_338,'#skF_2',C_342,D_154,E_343,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_343,u1_struct_0(C_342),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_343)
      | ~ m1_pre_topc(D_154,A_338)
      | v2_struct_0(D_154)
      | ~ m1_pre_topc(C_342,A_338)
      | v2_struct_0(C_342)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_154) ) ),
    inference(resolution,[status(thm)],[c_142,c_1033])).

tff(c_1058,plain,(
    ! [A_338,C_342,D_154,E_343] :
      ( v1_funct_1(k10_tmap_1(A_338,'#skF_2',C_342,D_154,E_343,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_343,u1_struct_0(C_342),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_343)
      | ~ m1_pre_topc(D_154,A_338)
      | v2_struct_0(D_154)
      | ~ m1_pre_topc(C_342,A_338)
      | v2_struct_0(C_342)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338)
      | ~ l1_struct_0(D_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_56,c_54,c_1043])).

tff(c_1757,plain,(
    ! [A_389,C_390,D_391,E_392] :
      ( v1_funct_1(k10_tmap_1(A_389,'#skF_2',C_390,D_391,E_392,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_391)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_391))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_390),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_390),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc(D_391,A_389)
      | v2_struct_0(D_391)
      | ~ m1_pre_topc(C_390,A_389)
      | v2_struct_0(C_390)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389)
      | ~ l1_struct_0(D_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1058])).

tff(c_1768,plain,(
    ! [C_70,D_391,A_389,D_71,A_68] :
      ( v1_funct_1(k10_tmap_1(A_389,'#skF_2',D_71,D_391,k2_tmap_1(A_68,'#skF_2',C_70,D_71),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_391)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_391))
      | ~ v1_funct_2(k2_tmap_1(A_68,'#skF_2',C_70,D_71),u1_struct_0(D_71),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_68,'#skF_2',C_70,D_71))
      | ~ m1_pre_topc(D_391,A_389)
      | v2_struct_0(D_391)
      | ~ m1_pre_topc(D_71,A_389)
      | v2_struct_0(D_71)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389)
      | ~ l1_struct_0(D_391)
      | ~ l1_struct_0(D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_26,c_1757])).

tff(c_2347,plain,(
    ! [A_454,A_455,C_452,D_451,D_453] :
      ( v1_funct_1(k10_tmap_1(A_454,'#skF_2',D_451,D_453,k2_tmap_1(A_455,'#skF_2',C_452,D_451),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_453)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_453))
      | ~ v1_funct_2(k2_tmap_1(A_455,'#skF_2',C_452,D_451),u1_struct_0(D_451),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_455,'#skF_2',C_452,D_451))
      | ~ m1_pre_topc(D_453,A_454)
      | v2_struct_0(D_453)
      | ~ m1_pre_topc(D_451,A_454)
      | v2_struct_0(D_451)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ l1_struct_0(D_453)
      | ~ l1_struct_0(D_451)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_452,u1_struct_0(A_455),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_452)
      | ~ l1_struct_0(A_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1768])).

tff(c_2362,plain,(
    ! [A_454,D_154,D_453] :
      ( v1_funct_1(k10_tmap_1(A_454,'#skF_2',D_154,D_453,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_453)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_453))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_154))
      | ~ m1_pre_topc(D_453,A_454)
      | v2_struct_0(D_453)
      | ~ m1_pre_topc(D_154,A_454)
      | v2_struct_0(D_154)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ l1_struct_0(D_453)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_154) ) ),
    inference(resolution,[status(thm)],[c_142,c_2347])).

tff(c_2384,plain,(
    ! [A_456,D_457,D_458] :
      ( v1_funct_1(k10_tmap_1(A_456,'#skF_2',D_457,D_458,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_457),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_458)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_458))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_457))
      | ~ m1_pre_topc(D_458,A_456)
      | v2_struct_0(D_458)
      | ~ m1_pre_topc(D_457,A_456)
      | v2_struct_0(D_457)
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456)
      | ~ l1_struct_0(D_458)
      | ~ l1_struct_0(D_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_42,c_40,c_38,c_2362])).

tff(c_34,plain,(
    ! [A_103] :
      ( m1_pre_topc(A_103,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_208,plain,(
    ! [E_184,B_185,D_187,A_186,C_183] :
      ( k3_tmap_1(A_186,B_185,C_183,D_187,E_184) = k2_partfun1(u1_struct_0(C_183),u1_struct_0(B_185),E_184,u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,C_183)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183),u1_struct_0(B_185))))
      | ~ v1_funct_2(E_184,u1_struct_0(C_183),u1_struct_0(B_185))
      | ~ v1_funct_1(E_184)
      | ~ m1_pre_topc(D_187,A_186)
      | ~ m1_pre_topc(C_183,A_186)
      | ~ l1_pre_topc(B_185)
      | ~ v2_pre_topc(B_185)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_212,plain,(
    ! [A_186,D_187] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_187,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_187,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_38,c_208])).

tff(c_216,plain,(
    ! [A_186,D_187] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_187,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,'#skF_1')
      | ~ m1_pre_topc(D_187,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_212])).

tff(c_219,plain,(
    ! [A_190,D_191] :
      ( k3_tmap_1(A_190,'#skF_2','#skF_1',D_191,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,'#skF_1')
      | ~ m1_pre_topc(D_191,A_190)
      | ~ m1_pre_topc('#skF_1',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_216])).

tff(c_223,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_219])).

tff(c_229,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_223])).

tff(c_230,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_229])).

tff(c_235,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_239,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_235])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_239])).

tff(c_244,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_183,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k2_partfun1(u1_struct_0(A_173),u1_struct_0(B_174),C_175,u1_struct_0(D_176)) = k2_tmap_1(A_173,B_174,C_175,D_176)
      | ~ m1_pre_topc(D_176,A_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173),u1_struct_0(B_174))))
      | ~ v1_funct_2(C_175,u1_struct_0(A_173),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ l1_pre_topc(B_174)
      | ~ v2_pre_topc(B_174)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_187,plain,(
    ! [D_176] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_176)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_176)
      | ~ m1_pre_topc(D_176,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_191,plain,(
    ! [D_176] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_176)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_176)
      | ~ m1_pre_topc(D_176,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_42,c_40,c_187])).

tff(c_192,plain,(
    ! [D_176] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_176)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_176)
      | ~ m1_pre_topc(D_176,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_191])).

tff(c_261,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_192])).

tff(c_268,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_261])).

tff(c_245,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_225,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_219])).

tff(c_233,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_225])).

tff(c_234,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_233])).

tff(c_324,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_234])).

tff(c_328,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_192])).

tff(c_335,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_328])).

tff(c_604,plain,(
    ! [C_244,B_245,E_243,A_242,D_246] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_242,C_244,D_246)),u1_struct_0(B_245),E_243,k10_tmap_1(A_242,B_245,C_244,D_246,k3_tmap_1(A_242,B_245,k1_tsep_1(A_242,C_244,D_246),C_244,E_243),k3_tmap_1(A_242,B_245,k1_tsep_1(A_242,C_244,D_246),D_246,E_243)))
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_242,C_244,D_246)),u1_struct_0(B_245))))
      | ~ v1_funct_2(E_243,u1_struct_0(k1_tsep_1(A_242,C_244,D_246)),u1_struct_0(B_245))
      | ~ v1_funct_1(E_243)
      | ~ m1_pre_topc(D_246,A_242)
      | v2_struct_0(D_246)
      | ~ m1_pre_topc(C_244,A_242)
      | v2_struct_0(C_244)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_609,plain,(
    ! [B_245,E_243] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_245),E_243,k10_tmap_1('#skF_1',B_245,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_245,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_243),k3_tmap_1('#skF_1',B_245,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_243)))
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_245))))
      | ~ v1_funct_2(E_243,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_245))
      | ~ v1_funct_1(E_243)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_604])).

tff(c_618,plain,(
    ! [B_245,E_243] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_245),E_243,k10_tmap_1('#skF_1',B_245,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_245,'#skF_1','#skF_3',E_243),k3_tmap_1('#skF_1',B_245,'#skF_1','#skF_4',E_243)))
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_245))))
      | ~ v1_funct_2(E_243,u1_struct_0('#skF_1'),u1_struct_0(B_245))
      | ~ v1_funct_1(E_243)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_44,c_44,c_44,c_44,c_609])).

tff(c_626,plain,(
    ! [B_247,E_248] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_247),E_248,k10_tmap_1('#skF_1',B_247,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_247,'#skF_1','#skF_3',E_248),k3_tmap_1('#skF_1',B_247,'#skF_1','#skF_4',E_248)))
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_247))))
      | ~ v1_funct_2(E_248,u1_struct_0('#skF_1'),u1_struct_0(B_247))
      | ~ v1_funct_1(E_248)
      | ~ l1_pre_topc(B_247)
      | ~ v2_pre_topc(B_247)
      | v2_struct_0(B_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_618])).

tff(c_631,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_626])).

tff(c_637,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_38,c_268,c_631])).

tff(c_638,plain,(
    r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_637])).

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

tff(c_643,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_638,c_4])).

tff(c_646,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_643])).

tff(c_658,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_2387,plain,
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
    inference(resolution,[status(thm)],[c_2384,c_658])).

tff(c_2390,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_62,c_60,c_50,c_46,c_2387])).

tff(c_2391,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_2390])).

tff(c_2392,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2391])).

tff(c_2455,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2392])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2455])).

tff(c_2461,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2391])).

tff(c_2460,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2391])).

tff(c_2462,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2460])).

tff(c_2473,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_2462])).

tff(c_2477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_2473])).

tff(c_2478,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2460])).

tff(c_2482,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_2478])).

tff(c_2486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2461,c_2482])).

tff(c_2488,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_472,plain,(
    ! [E_206,B_209,F_210,D_211,C_207,A_208] :
      ( m1_subset_1(k10_tmap_1(A_208,B_209,C_207,D_211,E_206,F_210),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208,C_207,D_211)),u1_struct_0(B_209))))
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_211),u1_struct_0(B_209))))
      | ~ v1_funct_2(F_210,u1_struct_0(D_211),u1_struct_0(B_209))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207),u1_struct_0(B_209))))
      | ~ v1_funct_2(E_206,u1_struct_0(C_207),u1_struct_0(B_209))
      | ~ v1_funct_1(E_206)
      | ~ m1_pre_topc(D_211,A_208)
      | v2_struct_0(D_211)
      | ~ m1_pre_topc(C_207,A_208)
      | v2_struct_0(C_207)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_489,plain,(
    ! [B_209,E_206,F_210] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_209,'#skF_3','#skF_4',E_206,F_210),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_209))))
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(F_210,u1_struct_0('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_209))))
      | ~ v1_funct_2(E_206,u1_struct_0('#skF_3'),u1_struct_0(B_209))
      | ~ v1_funct_1(E_206)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_472])).

tff(c_498,plain,(
    ! [B_209,E_206,F_210] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_209,'#skF_3','#skF_4',E_206,F_210),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_209))))
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(F_210,u1_struct_0('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_209))))
      | ~ v1_funct_2(E_206,u1_struct_0('#skF_3'),u1_struct_0(B_209))
      | ~ v1_funct_1(E_206)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_489])).

tff(c_499,plain,(
    ! [B_209,E_206,F_210] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_209,'#skF_3','#skF_4',E_206,F_210),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_209))))
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(F_210,u1_struct_0('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_209))))
      | ~ v1_funct_2(E_206,u1_struct_0('#skF_3'),u1_struct_0(B_209))
      | ~ v1_funct_1(E_206)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_498])).

tff(c_2487,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_2489,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2487])).

tff(c_2497,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_499,c_2489])).

tff(c_2500,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2497])).

tff(c_2501,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2500])).

tff(c_2502,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2501])).

tff(c_2506,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_2502])).

tff(c_2510,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2506])).

tff(c_2514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2510])).

tff(c_2515,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2501])).

tff(c_2517,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2515])).

tff(c_2520,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2517])).

tff(c_2523,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_2520])).

tff(c_2526,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2523])).

tff(c_2530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2526])).

tff(c_2532,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2515])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2609,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2532,c_2])).

tff(c_2610,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2614,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_2610])).

tff(c_2617,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2614])).

tff(c_2621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2617])).

tff(c_2623,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_2622,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_2624,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2622])).

tff(c_2628,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_2624])).

tff(c_2631,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2628])).

tff(c_2635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2631])).

tff(c_2637,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2622])).

tff(c_2531,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2515])).

tff(c_2723,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_2637,c_2531])).

tff(c_2724,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2723])).

tff(c_2728,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_2724])).

tff(c_2731,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2728])).

tff(c_2735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2731])).

tff(c_2736,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2723])).

tff(c_2766,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2736])).

tff(c_2769,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_2766])).

tff(c_2772,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2769])).

tff(c_2776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2772])).

tff(c_2778,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2487])).

tff(c_282,plain,(
    ! [A_194,C_193,E_192] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2',C_193,'#skF_1',E_192,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_192,u1_struct_0(C_193),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_192)
      | ~ m1_pre_topc('#skF_1',A_194)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_193,A_194)
      | v2_struct_0(C_193)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_38,c_278])).

tff(c_286,plain,(
    ! [A_194,C_193,E_192] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2',C_193,'#skF_1',E_192,'#skF_5'))
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_192,u1_struct_0(C_193),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_192)
      | ~ m1_pre_topc('#skF_1',A_194)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_193,A_194)
      | v2_struct_0(C_193)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_282])).

tff(c_287,plain,(
    ! [A_194,C_193,E_192] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2',C_193,'#skF_1',E_192,'#skF_5'))
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_192,u1_struct_0(C_193),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_192)
      | ~ m1_pre_topc('#skF_1',A_194)
      | ~ m1_pre_topc(C_193,A_194)
      | v2_struct_0(C_193)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_286])).

tff(c_2782,plain,(
    ! [A_194] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_194)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_2778,c_287])).

tff(c_2803,plain,(
    ! [A_194] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_1',A_194)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2782])).

tff(c_2804,plain,(
    ! [A_194] :
      ( v1_funct_1(k10_tmap_1(A_194,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_1',A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2803])).

tff(c_2830,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2804])).

tff(c_2853,plain,
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
    inference(resolution,[status(thm)],[c_2847,c_2830])).

tff(c_2862,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_56,c_54,c_2853])).

tff(c_2863,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2862])).

tff(c_2865,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2863])).

tff(c_2893,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_2865])).

tff(c_2896,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2893])).

tff(c_2900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2896])).

tff(c_2901,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2863])).

tff(c_2910,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2901])).

tff(c_2913,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_2910])).

tff(c_2917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_2913])).

tff(c_2919,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_162,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( m1_subset_1(k2_tmap_1(A_163,B_164,C_165,D_166),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_166),u1_struct_0(B_164))))
      | ~ l1_struct_0(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_165,u1_struct_0(A_163),u1_struct_0(B_164))
      | ~ v1_funct_1(C_165)
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_30,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( v1_funct_1(k2_tmap_1(A_68,B_69,C_70,D_71))
      | ~ l1_struct_0(D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_69))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ v1_funct_1(C_70)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_173,plain,(
    ! [A_163,C_165,D_166,B_164,D_71] :
      ( v1_funct_1(k2_tmap_1(D_166,B_164,k2_tmap_1(A_163,B_164,C_165,D_166),D_71))
      | ~ l1_struct_0(D_71)
      | ~ v1_funct_2(k2_tmap_1(A_163,B_164,C_165,D_166),u1_struct_0(D_166),u1_struct_0(B_164))
      | ~ v1_funct_1(k2_tmap_1(A_163,B_164,C_165,D_166))
      | ~ l1_struct_0(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_165,u1_struct_0(A_163),u1_struct_0(B_164))
      | ~ v1_funct_1(C_165)
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_162,c_30])).

tff(c_2923,plain,(
    ! [D_71] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_71))
      | ~ l1_struct_0(D_71)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2919,c_173])).

tff(c_2930,plain,(
    ! [D_71] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_71))
      | ~ l1_struct_0(D_71)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_2846,c_2923])).

tff(c_2931,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2930])).

tff(c_2934,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_2931])).

tff(c_2938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_2934])).

tff(c_2940,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2930])).

tff(c_2918,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_2967,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2918])).

tff(c_2968,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2967])).

tff(c_2975,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_2968])).

tff(c_2978,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2975])).

tff(c_2982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2978])).

tff(c_2983,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2967])).

tff(c_2998,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2983])).

tff(c_3001,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_128,c_42,c_40,c_38,c_2998])).

tff(c_3004,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3001])).

tff(c_3008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3004])).

tff(c_3010,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2804])).

tff(c_2777,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2487])).

tff(c_3024,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_2777])).

tff(c_36,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_65,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_3030,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_65])).

tff(c_3066,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_159,c_3030])).

tff(c_3069,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3066])).

tff(c_3071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_3069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.68  
% 7.43/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.68  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.43/2.68  
% 7.43/2.68  %Foreground sorts:
% 7.43/2.68  
% 7.43/2.68  
% 7.43/2.68  %Background operators:
% 7.43/2.68  
% 7.43/2.68  
% 7.43/2.68  %Foreground operators:
% 7.43/2.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.43/2.68  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.43/2.68  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.43/2.68  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.43/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.43/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.43/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.43/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.43/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.43/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.43/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.43/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.43/2.68  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.43/2.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.43/2.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.43/2.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.43/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.43/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.43/2.68  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.43/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.68  
% 7.94/2.71  tff(f_280, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_tmap_1)).
% 7.94/2.71  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.94/2.71  tff(f_201, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 7.94/2.71  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 7.94/2.71  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.94/2.71  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.94/2.71  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.94/2.71  tff(f_241, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.94/2.71  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.94/2.71  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.94/2.71  tff(f_237, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_tmap_1)).
% 7.94/2.71  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.94/2.71  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.94/2.71  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_96, plain, (![A_138, B_139, C_140, D_141]: (v1_funct_1(k2_tmap_1(A_138, B_139, C_140, D_141)) | ~l1_struct_0(D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138), u1_struct_0(B_139)))) | ~v1_funct_2(C_140, u1_struct_0(A_138), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~l1_struct_0(B_139) | ~l1_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.94/2.71  tff(c_98, plain, (![D_141]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_141)) | ~l1_struct_0(D_141) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_96])).
% 7.94/2.71  tff(c_101, plain, (![D_141]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_141)) | ~l1_struct_0(D_141) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_98])).
% 7.94/2.71  tff(c_102, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_101])).
% 7.94/2.71  tff(c_112, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_102])).
% 7.94/2.71  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_112])).
% 7.94/2.71  tff(c_117, plain, (![D_141]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_141)) | ~l1_struct_0(D_141))), inference(splitRight, [status(thm)], [c_101])).
% 7.94/2.71  tff(c_119, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_117])).
% 7.94/2.71  tff(c_122, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_119])).
% 7.94/2.71  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_122])).
% 7.94/2.71  tff(c_128, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_117])).
% 7.94/2.71  tff(c_144, plain, (![C_160, D_158, B_156, F_159, A_157]: (r1_funct_2(A_157, B_156, C_160, D_158, F_159, F_159) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(C_160, D_158))) | ~v1_funct_2(F_159, C_160, D_158) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2(F_159, A_157, B_156) | ~v1_funct_1(F_159) | v1_xboole_0(D_158) | v1_xboole_0(B_156))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.71  tff(c_146, plain, (![A_157, B_156]: (r1_funct_2(A_157, B_156, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2('#skF_5', A_157, B_156) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_156))), inference(resolution, [status(thm)], [c_38, c_144])).
% 7.94/2.71  tff(c_149, plain, (![A_157, B_156]: (r1_funct_2(A_157, B_156, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2('#skF_5', A_157, B_156) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_146])).
% 7.94/2.71  tff(c_150, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_149])).
% 7.94/2.71  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.94/2.71  tff(c_153, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_150, c_10])).
% 7.94/2.71  tff(c_156, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_153])).
% 7.94/2.71  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_156])).
% 7.94/2.71  tff(c_160, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_149])).
% 7.94/2.71  tff(c_159, plain, (![A_157, B_156]: (r1_funct_2(A_157, B_156, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2('#skF_5', A_157, B_156) | v1_xboole_0(B_156))), inference(splitRight, [status(thm)], [c_149])).
% 7.94/2.71  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.71  tff(c_72, plain, (![B_132, A_133]: (l1_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.94/2.72  tff(c_81, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_72])).
% 7.94/2.72  tff(c_88, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_81])).
% 7.94/2.72  tff(c_118, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_101])).
% 7.94/2.72  tff(c_26, plain, (![A_68, B_69, C_70, D_71]: (m1_subset_1(k2_tmap_1(A_68, B_69, C_70, D_71), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71), u1_struct_0(B_69)))) | ~l1_struct_0(D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_69)))) | ~v1_funct_2(C_70, u1_struct_0(A_68), u1_struct_0(B_69)) | ~v1_funct_1(C_70) | ~l1_struct_0(B_69) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.94/2.72  tff(c_137, plain, (![A_151, B_152, C_153, D_154]: (v1_funct_2(k2_tmap_1(A_151, B_152, C_153, D_154), u1_struct_0(D_154), u1_struct_0(B_152)) | ~l1_struct_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151), u1_struct_0(B_152)))) | ~v1_funct_2(C_153, u1_struct_0(A_151), u1_struct_0(B_152)) | ~v1_funct_1(C_153) | ~l1_struct_0(B_152) | ~l1_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.94/2.72  tff(c_139, plain, (![D_154]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154), u1_struct_0(D_154), u1_struct_0('#skF_2')) | ~l1_struct_0(D_154) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_137])).
% 7.94/2.72  tff(c_142, plain, (![D_154]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154), u1_struct_0(D_154), u1_struct_0('#skF_2')) | ~l1_struct_0(D_154))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_139])).
% 7.94/2.72  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_78, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_72])).
% 7.94/2.72  tff(c_85, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78])).
% 7.94/2.72  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_44, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_378, plain, (![A_200, E_198, C_199, F_202, D_203, B_201]: (v1_funct_2(k10_tmap_1(A_200, B_201, C_199, D_203, E_198, F_202), u1_struct_0(k1_tsep_1(A_200, C_199, D_203)), u1_struct_0(B_201)) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_203), u1_struct_0(B_201)))) | ~v1_funct_2(F_202, u1_struct_0(D_203), u1_struct_0(B_201)) | ~v1_funct_1(F_202) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199), u1_struct_0(B_201)))) | ~v1_funct_2(E_198, u1_struct_0(C_199), u1_struct_0(B_201)) | ~v1_funct_1(E_198) | ~m1_pre_topc(D_203, A_200) | v2_struct_0(D_203) | ~m1_pre_topc(C_199, A_200) | v2_struct_0(C_199) | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.94/2.72  tff(c_381, plain, (![B_201, E_198, F_202]: (v1_funct_2(k10_tmap_1('#skF_1', B_201, '#skF_3', '#skF_4', E_198, F_202), u1_struct_0('#skF_1'), u1_struct_0(B_201)) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_201)))) | ~v1_funct_2(F_202, u1_struct_0('#skF_4'), u1_struct_0(B_201)) | ~v1_funct_1(F_202) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_201)))) | ~v1_funct_2(E_198, u1_struct_0('#skF_3'), u1_struct_0(B_201)) | ~v1_funct_1(E_198) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_378])).
% 7.94/2.72  tff(c_383, plain, (![B_201, E_198, F_202]: (v1_funct_2(k10_tmap_1('#skF_1', B_201, '#skF_3', '#skF_4', E_198, F_202), u1_struct_0('#skF_1'), u1_struct_0(B_201)) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_201)))) | ~v1_funct_2(F_202, u1_struct_0('#skF_4'), u1_struct_0(B_201)) | ~v1_funct_1(F_202) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_201)))) | ~v1_funct_2(E_198, u1_struct_0('#skF_3'), u1_struct_0(B_201)) | ~v1_funct_1(E_198) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_381])).
% 7.94/2.72  tff(c_521, plain, (![B_216, E_217, F_218]: (v1_funct_2(k10_tmap_1('#skF_1', B_216, '#skF_3', '#skF_4', E_217, F_218), u1_struct_0('#skF_1'), u1_struct_0(B_216)) | ~m1_subset_1(F_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_216)))) | ~v1_funct_2(F_218, u1_struct_0('#skF_4'), u1_struct_0(B_216)) | ~v1_funct_1(F_218) | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_216)))) | ~v1_funct_2(E_217, u1_struct_0('#skF_3'), u1_struct_0(B_216)) | ~v1_funct_1(E_217) | ~l1_pre_topc(B_216) | ~v2_pre_topc(B_216) | v2_struct_0(B_216))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_383])).
% 7.94/2.72  tff(c_525, plain, (![B_69, E_217, A_68, C_70]: (v1_funct_2(k10_tmap_1('#skF_1', B_69, '#skF_3', '#skF_4', E_217, k2_tmap_1(A_68, B_69, C_70, '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0(B_69)) | ~v1_funct_2(k2_tmap_1(A_68, B_69, C_70, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(B_69)) | ~v1_funct_1(k2_tmap_1(A_68, B_69, C_70, '#skF_4')) | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_69)))) | ~v1_funct_2(E_217, u1_struct_0('#skF_3'), u1_struct_0(B_69)) | ~v1_funct_1(E_217) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69) | ~l1_struct_0('#skF_4') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_69)))) | ~v1_funct_2(C_70, u1_struct_0(A_68), u1_struct_0(B_69)) | ~v1_funct_1(C_70) | ~l1_struct_0(B_69) | ~l1_struct_0(A_68))), inference(resolution, [status(thm)], [c_26, c_521])).
% 7.94/2.72  tff(c_2837, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_525])).
% 7.94/2.72  tff(c_2840, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2837])).
% 7.94/2.72  tff(c_2844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_2840])).
% 7.94/2.72  tff(c_2846, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_525])).
% 7.94/2.72  tff(c_127, plain, (![D_141]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_141)) | ~l1_struct_0(D_141))), inference(splitRight, [status(thm)], [c_117])).
% 7.94/2.72  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_2847, plain, (![B_516, E_517, A_518, C_519]: (v1_funct_2(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', E_517, k2_tmap_1(A_518, B_516, C_519, '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0(B_516)) | ~v1_funct_2(k2_tmap_1(A_518, B_516, C_519, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(B_516)) | ~v1_funct_1(k2_tmap_1(A_518, B_516, C_519, '#skF_4')) | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_516)))) | ~v1_funct_2(E_517, u1_struct_0('#skF_3'), u1_struct_0(B_516)) | ~v1_funct_1(E_517) | ~l1_pre_topc(B_516) | ~v2_pre_topc(B_516) | v2_struct_0(B_516) | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_518), u1_struct_0(B_516)))) | ~v1_funct_2(C_519, u1_struct_0(A_518), u1_struct_0(B_516)) | ~v1_funct_1(C_519) | ~l1_struct_0(B_516) | ~l1_struct_0(A_518))), inference(splitRight, [status(thm)], [c_525])).
% 7.94/2.72  tff(c_665, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_525])).
% 7.94/2.72  tff(c_668, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_665])).
% 7.94/2.72  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_668])).
% 7.94/2.72  tff(c_674, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_525])).
% 7.94/2.72  tff(c_278, plain, (![C_193, F_196, A_194, D_197, E_192, B_195]: (v1_funct_1(k10_tmap_1(A_194, B_195, C_193, D_197, E_192, F_196)) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_197), u1_struct_0(B_195)))) | ~v1_funct_2(F_196, u1_struct_0(D_197), u1_struct_0(B_195)) | ~v1_funct_1(F_196) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193), u1_struct_0(B_195)))) | ~v1_funct_2(E_192, u1_struct_0(C_193), u1_struct_0(B_195)) | ~v1_funct_1(E_192) | ~m1_pre_topc(D_197, A_194) | v2_struct_0(D_197) | ~m1_pre_topc(C_193, A_194) | v2_struct_0(C_193) | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.94/2.72  tff(c_1033, plain, (![C_342, B_341, D_339, A_344, C_340, A_338, E_343]: (v1_funct_1(k10_tmap_1(A_338, B_341, C_342, D_339, E_343, k2_tmap_1(A_344, B_341, C_340, D_339))) | ~v1_funct_2(k2_tmap_1(A_344, B_341, C_340, D_339), u1_struct_0(D_339), u1_struct_0(B_341)) | ~v1_funct_1(k2_tmap_1(A_344, B_341, C_340, D_339)) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0(B_341)))) | ~v1_funct_2(E_343, u1_struct_0(C_342), u1_struct_0(B_341)) | ~v1_funct_1(E_343) | ~m1_pre_topc(D_339, A_338) | v2_struct_0(D_339) | ~m1_pre_topc(C_342, A_338) | v2_struct_0(C_342) | ~l1_pre_topc(B_341) | ~v2_pre_topc(B_341) | v2_struct_0(B_341) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338) | ~l1_struct_0(D_339) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344), u1_struct_0(B_341)))) | ~v1_funct_2(C_340, u1_struct_0(A_344), u1_struct_0(B_341)) | ~v1_funct_1(C_340) | ~l1_struct_0(B_341) | ~l1_struct_0(A_344))), inference(resolution, [status(thm)], [c_26, c_278])).
% 7.94/2.72  tff(c_1043, plain, (![A_338, C_342, D_154, E_343]: (v1_funct_1(k10_tmap_1(A_338, '#skF_2', C_342, D_154, E_343, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_343, u1_struct_0(C_342), u1_struct_0('#skF_2')) | ~v1_funct_1(E_343) | ~m1_pre_topc(D_154, A_338) | v2_struct_0(D_154) | ~m1_pre_topc(C_342, A_338) | v2_struct_0(C_342) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_154))), inference(resolution, [status(thm)], [c_142, c_1033])).
% 7.94/2.72  tff(c_1058, plain, (![A_338, C_342, D_154, E_343]: (v1_funct_1(k10_tmap_1(A_338, '#skF_2', C_342, D_154, E_343, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_343, u1_struct_0(C_342), u1_struct_0('#skF_2')) | ~v1_funct_1(E_343) | ~m1_pre_topc(D_154, A_338) | v2_struct_0(D_154) | ~m1_pre_topc(C_342, A_338) | v2_struct_0(C_342) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338) | ~l1_struct_0(D_154))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_56, c_54, c_1043])).
% 7.94/2.72  tff(c_1757, plain, (![A_389, C_390, D_391, E_392]: (v1_funct_1(k10_tmap_1(A_389, '#skF_2', C_390, D_391, E_392, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_391))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_391)) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_390), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_392, u1_struct_0(C_390), u1_struct_0('#skF_2')) | ~v1_funct_1(E_392) | ~m1_pre_topc(D_391, A_389) | v2_struct_0(D_391) | ~m1_pre_topc(C_390, A_389) | v2_struct_0(C_390) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389) | ~l1_struct_0(D_391))), inference(negUnitSimplification, [status(thm)], [c_58, c_1058])).
% 7.94/2.72  tff(c_1768, plain, (![C_70, D_391, A_389, D_71, A_68]: (v1_funct_1(k10_tmap_1(A_389, '#skF_2', D_71, D_391, k2_tmap_1(A_68, '#skF_2', C_70, D_71), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_391))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_391)) | ~v1_funct_2(k2_tmap_1(A_68, '#skF_2', C_70, D_71), u1_struct_0(D_71), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_68, '#skF_2', C_70, D_71)) | ~m1_pre_topc(D_391, A_389) | v2_struct_0(D_391) | ~m1_pre_topc(D_71, A_389) | v2_struct_0(D_71) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389) | ~l1_struct_0(D_391) | ~l1_struct_0(D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_70, u1_struct_0(A_68), u1_struct_0('#skF_2')) | ~v1_funct_1(C_70) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_68))), inference(resolution, [status(thm)], [c_26, c_1757])).
% 7.94/2.72  tff(c_2347, plain, (![A_454, A_455, C_452, D_451, D_453]: (v1_funct_1(k10_tmap_1(A_454, '#skF_2', D_451, D_453, k2_tmap_1(A_455, '#skF_2', C_452, D_451), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_453))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_453)) | ~v1_funct_2(k2_tmap_1(A_455, '#skF_2', C_452, D_451), u1_struct_0(D_451), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_455, '#skF_2', C_452, D_451)) | ~m1_pre_topc(D_453, A_454) | v2_struct_0(D_453) | ~m1_pre_topc(D_451, A_454) | v2_struct_0(D_451) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~l1_struct_0(D_453) | ~l1_struct_0(D_451) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_452, u1_struct_0(A_455), u1_struct_0('#skF_2')) | ~v1_funct_1(C_452) | ~l1_struct_0(A_455))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1768])).
% 7.94/2.72  tff(c_2362, plain, (![A_454, D_154, D_453]: (v1_funct_1(k10_tmap_1(A_454, '#skF_2', D_154, D_453, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_453))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_453)) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_154)) | ~m1_pre_topc(D_453, A_454) | v2_struct_0(D_453) | ~m1_pre_topc(D_154, A_454) | v2_struct_0(D_154) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~l1_struct_0(D_453) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_154))), inference(resolution, [status(thm)], [c_142, c_2347])).
% 7.94/2.72  tff(c_2384, plain, (![A_456, D_457, D_458]: (v1_funct_1(k10_tmap_1(A_456, '#skF_2', D_457, D_458, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_457), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_458))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_458)) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_457)) | ~m1_pre_topc(D_458, A_456) | v2_struct_0(D_458) | ~m1_pre_topc(D_457, A_456) | v2_struct_0(D_457) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456) | ~l1_struct_0(D_458) | ~l1_struct_0(D_457))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_42, c_40, c_38, c_2362])).
% 7.94/2.72  tff(c_34, plain, (![A_103]: (m1_pre_topc(A_103, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.94/2.72  tff(c_208, plain, (![E_184, B_185, D_187, A_186, C_183]: (k3_tmap_1(A_186, B_185, C_183, D_187, E_184)=k2_partfun1(u1_struct_0(C_183), u1_struct_0(B_185), E_184, u1_struct_0(D_187)) | ~m1_pre_topc(D_187, C_183) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183), u1_struct_0(B_185)))) | ~v1_funct_2(E_184, u1_struct_0(C_183), u1_struct_0(B_185)) | ~v1_funct_1(E_184) | ~m1_pre_topc(D_187, A_186) | ~m1_pre_topc(C_183, A_186) | ~l1_pre_topc(B_185) | ~v2_pre_topc(B_185) | v2_struct_0(B_185) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.94/2.72  tff(c_212, plain, (![A_186, D_187]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_187, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_187)) | ~m1_pre_topc(D_187, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_187, A_186) | ~m1_pre_topc('#skF_1', A_186) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_38, c_208])).
% 7.94/2.72  tff(c_216, plain, (![A_186, D_187]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_187, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_187)) | ~m1_pre_topc(D_187, '#skF_1') | ~m1_pre_topc(D_187, A_186) | ~m1_pre_topc('#skF_1', A_186) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_212])).
% 7.94/2.72  tff(c_219, plain, (![A_190, D_191]: (k3_tmap_1(A_190, '#skF_2', '#skF_1', D_191, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_191)) | ~m1_pre_topc(D_191, '#skF_1') | ~m1_pre_topc(D_191, A_190) | ~m1_pre_topc('#skF_1', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(negUnitSimplification, [status(thm)], [c_58, c_216])).
% 7.94/2.72  tff(c_223, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_219])).
% 7.94/2.72  tff(c_229, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_223])).
% 7.94/2.72  tff(c_230, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_229])).
% 7.94/2.72  tff(c_235, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_230])).
% 7.94/2.72  tff(c_239, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_235])).
% 7.94/2.72  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_239])).
% 7.94/2.72  tff(c_244, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_230])).
% 7.94/2.72  tff(c_183, plain, (![A_173, B_174, C_175, D_176]: (k2_partfun1(u1_struct_0(A_173), u1_struct_0(B_174), C_175, u1_struct_0(D_176))=k2_tmap_1(A_173, B_174, C_175, D_176) | ~m1_pre_topc(D_176, A_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173), u1_struct_0(B_174)))) | ~v1_funct_2(C_175, u1_struct_0(A_173), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~l1_pre_topc(B_174) | ~v2_pre_topc(B_174) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.94/2.72  tff(c_187, plain, (![D_176]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_176))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_176) | ~m1_pre_topc(D_176, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_183])).
% 7.94/2.72  tff(c_191, plain, (![D_176]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_176))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_176) | ~m1_pre_topc(D_176, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_42, c_40, c_187])).
% 7.94/2.72  tff(c_192, plain, (![D_176]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_176))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_176) | ~m1_pre_topc(D_176, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_191])).
% 7.94/2.72  tff(c_261, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_244, c_192])).
% 7.94/2.72  tff(c_268, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_261])).
% 7.94/2.72  tff(c_245, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_230])).
% 7.94/2.72  tff(c_225, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_219])).
% 7.94/2.72  tff(c_233, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_225])).
% 7.94/2.72  tff(c_234, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_233])).
% 7.94/2.72  tff(c_324, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_234])).
% 7.94/2.72  tff(c_328, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_324, c_192])).
% 7.94/2.72  tff(c_335, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_328])).
% 7.94/2.72  tff(c_604, plain, (![C_244, B_245, E_243, A_242, D_246]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_242, C_244, D_246)), u1_struct_0(B_245), E_243, k10_tmap_1(A_242, B_245, C_244, D_246, k3_tmap_1(A_242, B_245, k1_tsep_1(A_242, C_244, D_246), C_244, E_243), k3_tmap_1(A_242, B_245, k1_tsep_1(A_242, C_244, D_246), D_246, E_243))) | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_242, C_244, D_246)), u1_struct_0(B_245)))) | ~v1_funct_2(E_243, u1_struct_0(k1_tsep_1(A_242, C_244, D_246)), u1_struct_0(B_245)) | ~v1_funct_1(E_243) | ~m1_pre_topc(D_246, A_242) | v2_struct_0(D_246) | ~m1_pre_topc(C_244, A_242) | v2_struct_0(C_244) | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.94/2.72  tff(c_609, plain, (![B_245, E_243]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_245), E_243, k10_tmap_1('#skF_1', B_245, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_245, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_243), k3_tmap_1('#skF_1', B_245, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_243))) | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_245)))) | ~v1_funct_2(E_243, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_245)) | ~v1_funct_1(E_243) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_604])).
% 7.94/2.72  tff(c_618, plain, (![B_245, E_243]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_245), E_243, k10_tmap_1('#skF_1', B_245, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_245, '#skF_1', '#skF_3', E_243), k3_tmap_1('#skF_1', B_245, '#skF_1', '#skF_4', E_243))) | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_245)))) | ~v1_funct_2(E_243, u1_struct_0('#skF_1'), u1_struct_0(B_245)) | ~v1_funct_1(E_243) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_44, c_44, c_44, c_44, c_609])).
% 7.94/2.72  tff(c_626, plain, (![B_247, E_248]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0(B_247), E_248, k10_tmap_1('#skF_1', B_247, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_247, '#skF_1', '#skF_3', E_248), k3_tmap_1('#skF_1', B_247, '#skF_1', '#skF_4', E_248))) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_247)))) | ~v1_funct_2(E_248, u1_struct_0('#skF_1'), u1_struct_0(B_247)) | ~v1_funct_1(E_248) | ~l1_pre_topc(B_247) | ~v2_pre_topc(B_247) | v2_struct_0(B_247))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_618])).
% 7.94/2.72  tff(c_631, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_626])).
% 7.94/2.72  tff(c_637, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_38, c_268, c_631])).
% 7.94/2.72  tff(c_638, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_637])).
% 7.94/2.72  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.94/2.72  tff(c_643, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_638, c_4])).
% 7.94/2.72  tff(c_646, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_643])).
% 7.94/2.72  tff(c_658, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_646])).
% 7.94/2.72  tff(c_2387, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2384, c_658])).
% 7.94/2.72  tff(c_2390, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_62, c_60, c_50, c_46, c_2387])).
% 7.94/2.72  tff(c_2391, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_2390])).
% 7.94/2.72  tff(c_2392, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2391])).
% 7.94/2.72  tff(c_2455, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2392])).
% 7.94/2.72  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2455])).
% 7.94/2.72  tff(c_2461, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2391])).
% 7.94/2.72  tff(c_2460, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_2391])).
% 7.94/2.72  tff(c_2462, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2460])).
% 7.94/2.72  tff(c_2473, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_127, c_2462])).
% 7.94/2.72  tff(c_2477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_2473])).
% 7.94/2.72  tff(c_2478, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_2460])).
% 7.94/2.72  tff(c_2482, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_127, c_2478])).
% 7.94/2.72  tff(c_2486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2461, c_2482])).
% 7.94/2.72  tff(c_2488, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_646])).
% 7.94/2.72  tff(c_472, plain, (![E_206, B_209, F_210, D_211, C_207, A_208]: (m1_subset_1(k10_tmap_1(A_208, B_209, C_207, D_211, E_206, F_210), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208, C_207, D_211)), u1_struct_0(B_209)))) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_211), u1_struct_0(B_209)))) | ~v1_funct_2(F_210, u1_struct_0(D_211), u1_struct_0(B_209)) | ~v1_funct_1(F_210) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207), u1_struct_0(B_209)))) | ~v1_funct_2(E_206, u1_struct_0(C_207), u1_struct_0(B_209)) | ~v1_funct_1(E_206) | ~m1_pre_topc(D_211, A_208) | v2_struct_0(D_211) | ~m1_pre_topc(C_207, A_208) | v2_struct_0(C_207) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.94/2.72  tff(c_489, plain, (![B_209, E_206, F_210]: (m1_subset_1(k10_tmap_1('#skF_1', B_209, '#skF_3', '#skF_4', E_206, F_210), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_209)))) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(F_210, u1_struct_0('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(F_210) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_209)))) | ~v1_funct_2(E_206, u1_struct_0('#skF_3'), u1_struct_0(B_209)) | ~v1_funct_1(E_206) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_472])).
% 7.94/2.72  tff(c_498, plain, (![B_209, E_206, F_210]: (m1_subset_1(k10_tmap_1('#skF_1', B_209, '#skF_3', '#skF_4', E_206, F_210), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_209)))) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(F_210, u1_struct_0('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(F_210) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_209)))) | ~v1_funct_2(E_206, u1_struct_0('#skF_3'), u1_struct_0(B_209)) | ~v1_funct_1(E_206) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_489])).
% 7.94/2.72  tff(c_499, plain, (![B_209, E_206, F_210]: (m1_subset_1(k10_tmap_1('#skF_1', B_209, '#skF_3', '#skF_4', E_206, F_210), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_209)))) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(F_210, u1_struct_0('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(F_210) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_209)))) | ~v1_funct_2(E_206, u1_struct_0('#skF_3'), u1_struct_0(B_209)) | ~v1_funct_1(E_206) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_498])).
% 7.94/2.72  tff(c_2487, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_646])).
% 7.94/2.72  tff(c_2489, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2487])).
% 7.94/2.72  tff(c_2497, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_499, c_2489])).
% 7.94/2.72  tff(c_2500, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2497])).
% 7.94/2.72  tff(c_2501, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2500])).
% 7.94/2.72  tff(c_2502, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2501])).
% 7.94/2.72  tff(c_2506, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_127, c_2502])).
% 7.94/2.72  tff(c_2510, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2506])).
% 7.94/2.72  tff(c_2514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2510])).
% 7.94/2.72  tff(c_2515, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2501])).
% 7.94/2.72  tff(c_2517, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2515])).
% 7.94/2.72  tff(c_2520, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2517])).
% 7.94/2.72  tff(c_2523, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_2520])).
% 7.94/2.72  tff(c_2526, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2523])).
% 7.94/2.72  tff(c_2530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_2526])).
% 7.94/2.72  tff(c_2532, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2515])).
% 7.94/2.72  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.94/2.72  tff(c_2609, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_2532, c_2])).
% 7.94/2.72  tff(c_2610, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2609])).
% 7.94/2.72  tff(c_2614, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_127, c_2610])).
% 7.94/2.72  tff(c_2617, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2614])).
% 7.94/2.72  tff(c_2621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_2617])).
% 7.94/2.72  tff(c_2623, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_2609])).
% 7.94/2.72  tff(c_2622, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_2609])).
% 7.94/2.72  tff(c_2624, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2622])).
% 7.94/2.72  tff(c_2628, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_142, c_2624])).
% 7.94/2.72  tff(c_2631, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2628])).
% 7.94/2.72  tff(c_2635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_2631])).
% 7.94/2.72  tff(c_2637, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2622])).
% 7.94/2.72  tff(c_2531, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2515])).
% 7.94/2.72  tff(c_2723, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_2637, c_2531])).
% 7.94/2.72  tff(c_2724, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2723])).
% 7.94/2.72  tff(c_2728, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_142, c_2724])).
% 7.94/2.72  tff(c_2731, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2728])).
% 7.94/2.72  tff(c_2735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2731])).
% 7.94/2.72  tff(c_2736, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2723])).
% 7.94/2.72  tff(c_2766, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2736])).
% 7.94/2.72  tff(c_2769, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_2766])).
% 7.94/2.72  tff(c_2772, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2769])).
% 7.94/2.72  tff(c_2776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2772])).
% 7.94/2.72  tff(c_2778, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2487])).
% 7.94/2.72  tff(c_282, plain, (![A_194, C_193, E_192]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', C_193, '#skF_1', E_192, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_192, u1_struct_0(C_193), u1_struct_0('#skF_2')) | ~v1_funct_1(E_192) | ~m1_pre_topc('#skF_1', A_194) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_193, A_194) | v2_struct_0(C_193) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(resolution, [status(thm)], [c_38, c_278])).
% 7.94/2.72  tff(c_286, plain, (![A_194, C_193, E_192]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', C_193, '#skF_1', E_192, '#skF_5')) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_192, u1_struct_0(C_193), u1_struct_0('#skF_2')) | ~v1_funct_1(E_192) | ~m1_pre_topc('#skF_1', A_194) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_193, A_194) | v2_struct_0(C_193) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_282])).
% 7.94/2.72  tff(c_287, plain, (![A_194, C_193, E_192]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', C_193, '#skF_1', E_192, '#skF_5')) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_193), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_192, u1_struct_0(C_193), u1_struct_0('#skF_2')) | ~v1_funct_1(E_192) | ~m1_pre_topc('#skF_1', A_194) | ~m1_pre_topc(C_193, A_194) | v2_struct_0(C_193) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_286])).
% 7.94/2.72  tff(c_2782, plain, (![A_194]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_194) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(resolution, [status(thm)], [c_2778, c_287])).
% 7.94/2.72  tff(c_2803, plain, (![A_194]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_1', A_194) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2782])).
% 7.94/2.72  tff(c_2804, plain, (![A_194]: (v1_funct_1(k10_tmap_1(A_194, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_1', A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_64, c_2803])).
% 7.94/2.72  tff(c_2830, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2804])).
% 7.94/2.72  tff(c_2853, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2847, c_2830])).
% 7.94/2.72  tff(c_2862, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_56, c_54, c_2853])).
% 7.94/2.72  tff(c_2863, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2862])).
% 7.94/2.72  tff(c_2865, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2863])).
% 7.94/2.72  tff(c_2893, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_127, c_2865])).
% 7.94/2.72  tff(c_2896, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2893])).
% 7.94/2.72  tff(c_2900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2896])).
% 7.94/2.72  tff(c_2901, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2863])).
% 7.94/2.72  tff(c_2910, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2901])).
% 7.94/2.72  tff(c_2913, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_142, c_2910])).
% 7.94/2.72  tff(c_2917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2846, c_2913])).
% 7.94/2.72  tff(c_2919, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2901])).
% 7.94/2.72  tff(c_162, plain, (![A_163, B_164, C_165, D_166]: (m1_subset_1(k2_tmap_1(A_163, B_164, C_165, D_166), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_166), u1_struct_0(B_164)))) | ~l1_struct_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163), u1_struct_0(B_164)))) | ~v1_funct_2(C_165, u1_struct_0(A_163), u1_struct_0(B_164)) | ~v1_funct_1(C_165) | ~l1_struct_0(B_164) | ~l1_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.94/2.72  tff(c_30, plain, (![A_68, B_69, C_70, D_71]: (v1_funct_1(k2_tmap_1(A_68, B_69, C_70, D_71)) | ~l1_struct_0(D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_69)))) | ~v1_funct_2(C_70, u1_struct_0(A_68), u1_struct_0(B_69)) | ~v1_funct_1(C_70) | ~l1_struct_0(B_69) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.94/2.72  tff(c_173, plain, (![A_163, C_165, D_166, B_164, D_71]: (v1_funct_1(k2_tmap_1(D_166, B_164, k2_tmap_1(A_163, B_164, C_165, D_166), D_71)) | ~l1_struct_0(D_71) | ~v1_funct_2(k2_tmap_1(A_163, B_164, C_165, D_166), u1_struct_0(D_166), u1_struct_0(B_164)) | ~v1_funct_1(k2_tmap_1(A_163, B_164, C_165, D_166)) | ~l1_struct_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163), u1_struct_0(B_164)))) | ~v1_funct_2(C_165, u1_struct_0(A_163), u1_struct_0(B_164)) | ~v1_funct_1(C_165) | ~l1_struct_0(B_164) | ~l1_struct_0(A_163))), inference(resolution, [status(thm)], [c_162, c_30])).
% 7.94/2.72  tff(c_2923, plain, (![D_71]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_71)) | ~l1_struct_0(D_71) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2919, c_173])).
% 7.94/2.72  tff(c_2930, plain, (![D_71]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_71)) | ~l1_struct_0(D_71) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_2846, c_2923])).
% 7.94/2.72  tff(c_2931, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2930])).
% 7.94/2.72  tff(c_2934, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_127, c_2931])).
% 7.94/2.72  tff(c_2938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2846, c_2934])).
% 7.94/2.72  tff(c_2940, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_2930])).
% 7.94/2.72  tff(c_2918, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2901])).
% 7.94/2.72  tff(c_2967, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2918])).
% 7.94/2.72  tff(c_2968, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2967])).
% 7.94/2.72  tff(c_2975, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_142, c_2968])).
% 7.94/2.72  tff(c_2978, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2975])).
% 7.94/2.72  tff(c_2982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2978])).
% 7.94/2.72  tff(c_2983, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2967])).
% 7.94/2.72  tff(c_2998, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2983])).
% 7.94/2.72  tff(c_3001, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_128, c_42, c_40, c_38, c_2998])).
% 7.94/2.72  tff(c_3004, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_3001])).
% 7.94/2.72  tff(c_3008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_3004])).
% 7.94/2.72  tff(c_3010, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2804])).
% 7.94/2.72  tff(c_2777, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_2487])).
% 7.94/2.72  tff(c_3024, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_2777])).
% 7.94/2.72  tff(c_36, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_280])).
% 7.94/2.72  tff(c_65, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 7.94/2.72  tff(c_3030, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3024, c_65])).
% 7.94/2.72  tff(c_3066, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_159, c_3030])).
% 7.94/2.72  tff(c_3069, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3066])).
% 7.94/2.72  tff(c_3071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_3069])).
% 7.94/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.72  
% 7.94/2.72  Inference rules
% 7.94/2.72  ----------------------
% 7.94/2.72  #Ref     : 0
% 7.94/2.72  #Sup     : 530
% 7.94/2.72  #Fact    : 0
% 7.94/2.72  #Define  : 0
% 7.94/2.72  #Split   : 34
% 7.94/2.72  #Chain   : 0
% 7.94/2.72  #Close   : 0
% 7.94/2.72  
% 7.94/2.72  Ordering : KBO
% 7.94/2.72  
% 7.94/2.72  Simplification rules
% 7.94/2.72  ----------------------
% 7.94/2.72  #Subsume      : 135
% 7.94/2.72  #Demod        : 1392
% 7.94/2.72  #Tautology    : 131
% 7.94/2.72  #SimpNegUnit  : 187
% 7.94/2.72  #BackRed      : 9
% 7.94/2.72  
% 7.94/2.72  #Partial instantiations: 0
% 7.94/2.72  #Strategies tried      : 1
% 7.94/2.72  
% 7.94/2.72  Timing (in seconds)
% 7.94/2.72  ----------------------
% 7.94/2.72  Preprocessing        : 0.49
% 7.94/2.72  Parsing              : 0.27
% 7.94/2.72  CNF conversion       : 0.04
% 7.94/2.72  Main loop            : 1.33
% 7.94/2.72  Inferencing          : 0.45
% 7.94/2.72  Reduction            : 0.44
% 7.94/2.72  Demodulation         : 0.32
% 7.94/2.72  BG Simplification    : 0.05
% 7.94/2.72  Subsumption          : 0.33
% 7.94/2.72  Abstraction          : 0.07
% 7.94/2.72  MUC search           : 0.00
% 7.94/2.72  Cooper               : 0.00
% 7.94/2.72  Total                : 1.90
% 7.94/2.72  Index Insertion      : 0.00
% 7.94/2.72  Index Deletion       : 0.00
% 7.94/2.72  Index Matching       : 0.00
% 7.94/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
