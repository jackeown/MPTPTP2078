%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:10 EST 2020

% Result     : Theorem 12.30s
% Output     : CNFRefutation 12.45s
% Verified   : 
% Statistics : Number of formulae       :  177 (8466 expanded)
%              Number of leaves         :   38 (3369 expanded)
%              Depth                    :   29
%              Number of atoms          :  905 (65695 expanded)
%              Number of equality atoms :   36 (4832 expanded)
%              Maximal formula depth    :   24 (   7 average)
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

tff(f_285,negated_conjecture,(
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

tff(f_246,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_206,axiom,(
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

tff(f_242,axiom,(
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

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_84,plain,(
    ! [D_138,C_140,A_141,F_142,B_139] :
      ( r1_funct_2(A_141,B_139,C_140,D_138,F_142,F_142)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_140,D_138)))
      | ~ v1_funct_2(F_142,C_140,D_138)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_139)))
      | ~ v1_funct_2(F_142,A_141,B_139)
      | ~ v1_funct_1(F_142)
      | v1_xboole_0(D_138)
      | v1_xboole_0(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_141,B_139] :
      ( r1_funct_2(A_141,B_139,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_141,B_139)))
      | ~ v1_funct_2('#skF_5',A_141,B_139)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_139) ) ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_89,plain,(
    ! [A_141,B_139] :
      ( r1_funct_2(A_141,B_139,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_141,B_139)))
      | ~ v1_funct_2('#skF_5',A_141,B_139)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_86])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_93])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_105,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_104,plain,(
    ! [A_141,B_139] :
      ( r1_funct_2(A_141,B_139,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_141,B_139)))
      | ~ v1_funct_2('#skF_5',A_141,B_139)
      | v1_xboole_0(B_139) ) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_32,plain,(
    ! [A_101] :
      ( m1_pre_topc(A_101,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_163,plain,(
    ! [D_179,B_178,A_176,C_177,E_175] :
      ( k3_tmap_1(A_176,B_178,C_177,D_179,E_175) = k2_partfun1(u1_struct_0(C_177),u1_struct_0(B_178),E_175,u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,C_177)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_177),u1_struct_0(B_178))))
      | ~ v1_funct_2(E_175,u1_struct_0(C_177),u1_struct_0(B_178))
      | ~ v1_funct_1(E_175)
      | ~ m1_pre_topc(D_179,A_176)
      | ~ m1_pre_topc(C_177,A_176)
      | ~ l1_pre_topc(B_178)
      | ~ v2_pre_topc(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_167,plain,(
    ! [A_176,D_179] :
      ( k3_tmap_1(A_176,'#skF_2','#skF_1',D_179,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_179,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_171,plain,(
    ! [A_176,D_179] :
      ( k3_tmap_1(A_176,'#skF_2','#skF_1',D_179,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,'#skF_1')
      | ~ m1_pre_topc(D_179,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_167])).

tff(c_173,plain,(
    ! [A_180,D_181] :
      ( k3_tmap_1(A_180,'#skF_2','#skF_1',D_181,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181))
      | ~ m1_pre_topc(D_181,'#skF_1')
      | ~ m1_pre_topc(D_181,A_180)
      | ~ m1_pre_topc('#skF_1',A_180)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_171])).

tff(c_177,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_173])).

tff(c_183,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_177])).

tff(c_184,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_183])).

tff(c_189,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_192,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_192])).

tff(c_198,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_197,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_123,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k2_partfun1(u1_struct_0(A_158),u1_struct_0(B_159),C_160,u1_struct_0(D_161)) = k2_tmap_1(A_158,B_159,C_160,D_161)
      | ~ m1_pre_topc(D_161,A_158)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_159))))
      | ~ v1_funct_2(C_160,u1_struct_0(A_158),u1_struct_0(B_159))
      | ~ v1_funct_1(C_160)
      | ~ l1_pre_topc(B_159)
      | ~ v2_pre_topc(B_159)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_125,plain,(
    ! [D_161] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_161)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_161)
      | ~ m1_pre_topc(D_161,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_128,plain,(
    ! [D_161] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_161)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_161)
      | ~ m1_pre_topc(D_161,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_40,c_38,c_125])).

tff(c_129,plain,(
    ! [D_161] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_161)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_161)
      | ~ m1_pre_topc(D_161,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_128])).

tff(c_325,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_129])).

tff(c_332,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_325])).

tff(c_115,plain,(
    ! [E_155,C_152,A_154,D_151,B_153] :
      ( v1_funct_1(k3_tmap_1(A_154,B_153,C_152,D_151,E_155))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_152),u1_struct_0(B_153))))
      | ~ v1_funct_2(E_155,u1_struct_0(C_152),u1_struct_0(B_153))
      | ~ v1_funct_1(E_155)
      | ~ m1_pre_topc(D_151,A_154)
      | ~ m1_pre_topc(C_152,A_154)
      | ~ l1_pre_topc(B_153)
      | ~ v2_pre_topc(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_117,plain,(
    ! [A_154,D_151] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_151,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_151,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_120,plain,(
    ! [A_154,D_151] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_151,'#skF_5'))
      | ~ m1_pre_topc(D_151,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_117])).

tff(c_121,plain,(
    ! [A_154,D_151] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_151,'#skF_5'))
      | ~ m1_pre_topc(D_151,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_120])).

tff(c_346,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_121])).

tff(c_356,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_198,c_48,c_346])).

tff(c_357,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_356])).

tff(c_139,plain,(
    ! [A_166,E_167,B_165,C_164,D_163] :
      ( v1_funct_2(k3_tmap_1(A_166,B_165,C_164,D_163,E_167),u1_struct_0(D_163),u1_struct_0(B_165))
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_164),u1_struct_0(B_165))))
      | ~ v1_funct_2(E_167,u1_struct_0(C_164),u1_struct_0(B_165))
      | ~ v1_funct_1(E_167)
      | ~ m1_pre_topc(D_163,A_166)
      | ~ m1_pre_topc(C_164,A_166)
      | ~ l1_pre_topc(B_165)
      | ~ v2_pre_topc(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_141,plain,(
    ! [A_166,D_163] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_163,'#skF_5'),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_163,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_144,plain,(
    ! [A_166,D_163] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_163,'#skF_5'),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_163,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_141])).

tff(c_145,plain,(
    ! [A_166,D_163] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_163,'#skF_5'),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_163,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_144])).

tff(c_343,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_145])).

tff(c_353,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_198,c_48,c_343])).

tff(c_354,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_353])).

tff(c_24,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] :
      ( m1_subset_1(k3_tmap_1(A_65,B_66,C_67,D_68,E_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68),u1_struct_0(B_66))))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67),u1_struct_0(B_66))))
      | ~ v1_funct_2(E_69,u1_struct_0(C_67),u1_struct_0(B_66))
      | ~ v1_funct_1(E_69)
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc(C_67,A_65)
      | ~ l1_pre_topc(B_66)
      | ~ v2_pre_topc(B_66)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_340,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_332,c_24])).

tff(c_350,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_198,c_48,c_40,c_38,c_36,c_340])).

tff(c_351,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_350])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_179,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_173])).

tff(c_187,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_179])).

tff(c_188,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_187])).

tff(c_199,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_199])).

tff(c_208,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_220,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_129])).

tff(c_227,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_220])).

tff(c_251,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_121])).

tff(c_261,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_198,c_44,c_251])).

tff(c_262,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_261])).

tff(c_248,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_145])).

tff(c_258,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_198,c_44,c_248])).

tff(c_259,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_258])).

tff(c_245,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_227,c_24])).

tff(c_255,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_198,c_44,c_40,c_38,c_36,c_245])).

tff(c_256,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_255])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_42,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_487,plain,(
    ! [A_195,C_194,B_196,E_199,D_198,F_197] :
      ( m1_subset_1(k10_tmap_1(A_195,B_196,C_194,D_198,E_199,F_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_195,C_194,D_198)),u1_struct_0(B_196))))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0(D_198),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0(C_194),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | ~ m1_pre_topc(D_198,A_195)
      | v2_struct_0(D_198)
      | ~ m1_pre_topc(C_194,A_195)
      | v2_struct_0(C_194)
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_504,plain,(
    ! [B_196,E_199,F_197] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_196,'#skF_3','#skF_4',E_199,F_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_196))))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0('#skF_4'),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0('#skF_3'),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_487])).

tff(c_513,plain,(
    ! [B_196,E_199,F_197] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_196,'#skF_3','#skF_4',E_199,F_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_196))))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0('#skF_4'),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0('#skF_3'),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_504])).

tff(c_514,plain,(
    ! [B_196,E_199,F_197] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_196,'#skF_3','#skF_4',E_199,F_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_196))))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0('#skF_4'),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0('#skF_3'),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_513])).

tff(c_359,plain,(
    ! [D_192,E_193,C_188,B_190,F_191,A_189] :
      ( v1_funct_2(k10_tmap_1(A_189,B_190,C_188,D_192,E_193,F_191),u1_struct_0(k1_tsep_1(A_189,C_188,D_192)),u1_struct_0(B_190))
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_192),u1_struct_0(B_190))))
      | ~ v1_funct_2(F_191,u1_struct_0(D_192),u1_struct_0(B_190))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_188),u1_struct_0(B_190))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc(D_192,A_189)
      | v2_struct_0(D_192)
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_362,plain,(
    ! [B_190,E_193,F_191] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_190,'#skF_3','#skF_4',E_193,F_191),u1_struct_0('#skF_1'),u1_struct_0(B_190))
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_190))))
      | ~ v1_funct_2(F_191,u1_struct_0('#skF_4'),u1_struct_0(B_190))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_193,u1_struct_0('#skF_3'),u1_struct_0(B_190))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_359])).

tff(c_364,plain,(
    ! [B_190,E_193,F_191] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_190,'#skF_3','#skF_4',E_193,F_191),u1_struct_0('#skF_1'),u1_struct_0(B_190))
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_190))))
      | ~ v1_funct_2(F_191,u1_struct_0('#skF_4'),u1_struct_0(B_190))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_193,u1_struct_0('#skF_3'),u1_struct_0(B_190))
      | ~ v1_funct_1(E_193)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_362])).

tff(c_1103,plain,(
    ! [B_246,E_247,F_248] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_246,'#skF_3','#skF_4',E_247,F_248),u1_struct_0('#skF_1'),u1_struct_0(B_246))
      | ~ m1_subset_1(F_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_246))))
      | ~ v1_funct_2(F_248,u1_struct_0('#skF_4'),u1_struct_0(B_246))
      | ~ v1_funct_1(F_248)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_246))))
      | ~ v1_funct_2(E_247,u1_struct_0('#skF_3'),u1_struct_0(B_246))
      | ~ v1_funct_1(E_247)
      | ~ l1_pre_topc(B_246)
      | ~ v2_pre_topc(B_246)
      | v2_struct_0(B_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_364])).

tff(c_1114,plain,(
    ! [E_247] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_247,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_247)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_256,c_1103])).

tff(c_1132,plain,(
    ! [E_247] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_247,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_247)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_262,c_259,c_1114])).

tff(c_1133,plain,(
    ! [E_247] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_247,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1132])).

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

tff(c_265,plain,(
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
    inference(resolution,[status(thm)],[c_256,c_22])).

tff(c_280,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_262,c_259,c_265])).

tff(c_2047,plain,(
    ! [A_277,C_278,E_279] :
      ( v1_funct_1(k10_tmap_1(A_277,'#skF_2',C_278,'#skF_4',E_279,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_279,u1_struct_0(C_278),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_279)
      | ~ m1_pre_topc('#skF_4',A_277)
      | ~ m1_pre_topc(C_278,A_277)
      | v2_struct_0(C_278)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46,c_280])).

tff(c_2087,plain,(
    ! [A_277] :
      ( v1_funct_1(k10_tmap_1(A_277,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_277)
      | ~ m1_pre_topc('#skF_3',A_277)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_351,c_2047])).

tff(c_2142,plain,(
    ! [A_277] :
      ( v1_funct_1(k10_tmap_1(A_277,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_277)
      | ~ m1_pre_topc('#skF_3',A_277)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_354,c_2087])).

tff(c_2143,plain,(
    ! [A_277] :
      ( v1_funct_1(k10_tmap_1(A_277,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_277)
      | ~ m1_pre_topc('#skF_3',A_277)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2142])).

tff(c_1443,plain,(
    ! [B_257,E_258,F_259] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_257,'#skF_3','#skF_4',E_258,F_259),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_257))))
      | ~ m1_subset_1(F_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_257))))
      | ~ v1_funct_2(F_259,u1_struct_0('#skF_4'),u1_struct_0(B_257))
      | ~ v1_funct_1(F_259)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_257))))
      | ~ v1_funct_2(E_258,u1_struct_0('#skF_3'),u1_struct_0(B_257))
      | ~ v1_funct_1(E_258)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_513])).

tff(c_231,plain,(
    ! [C_182,F_185,D_186,A_183,B_184,E_187] :
      ( v1_funct_1(k10_tmap_1(A_183,B_184,C_182,D_186,E_187,F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_186),u1_struct_0(B_184))))
      | ~ v1_funct_2(F_185,u1_struct_0(D_186),u1_struct_0(B_184))
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182),u1_struct_0(B_184))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_182),u1_struct_0(B_184))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc(D_186,A_183)
      | v2_struct_0(D_186)
      | ~ m1_pre_topc(C_182,A_183)
      | v2_struct_0(C_182)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_235,plain,(
    ! [A_183,C_182,E_187] :
      ( v1_funct_1(k10_tmap_1(A_183,'#skF_2',C_182,'#skF_1',E_187,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_182),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc('#skF_1',A_183)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_182,A_183)
      | v2_struct_0(C_182)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_239,plain,(
    ! [A_183,C_182,E_187] :
      ( v1_funct_1(k10_tmap_1(A_183,'#skF_2',C_182,'#skF_1',E_187,'#skF_5'))
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_182),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc('#skF_1',A_183)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_182,A_183)
      | v2_struct_0(C_182)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_235])).

tff(c_240,plain,(
    ! [A_183,C_182,E_187] :
      ( v1_funct_1(k10_tmap_1(A_183,'#skF_2',C_182,'#skF_1',E_187,'#skF_5'))
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_182),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc('#skF_1',A_183)
      | ~ m1_pre_topc(C_182,A_183)
      | v2_struct_0(C_182)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_239])).

tff(c_1446,plain,(
    ! [A_183,E_258,F_259] :
      ( v1_funct_1(k10_tmap_1(A_183,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259))
      | ~ m1_pre_topc('#skF_1',A_183)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183)
      | ~ m1_subset_1(F_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_259,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_259)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_258,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_258)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1443,c_240])).

tff(c_1463,plain,(
    ! [A_183,E_258,F_259] :
      ( v1_funct_1(k10_tmap_1(A_183,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_258,F_259))
      | ~ m1_pre_topc('#skF_1',A_183)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183)
      | ~ m1_subset_1(F_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_259,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_259)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_258,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_258)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1446])).

tff(c_6910,plain,(
    ! [A_609,E_610,F_611] :
      ( v1_funct_1(k10_tmap_1(A_609,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_610,F_611),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_610,F_611),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_610,F_611))
      | ~ m1_pre_topc('#skF_1',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609)
      | ~ m1_subset_1(F_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_611,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_611)
      | ~ m1_subset_1(E_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_610,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_610) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_1463])).

tff(c_6912,plain,(
    ! [A_609,E_247] :
      ( v1_funct_1(k10_tmap_1(A_609,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_247,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_247,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_247) ) ),
    inference(resolution,[status(thm)],[c_1133,c_6910])).

tff(c_6939,plain,(
    ! [A_618,E_619] :
      ( v1_funct_1(k10_tmap_1(A_618,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_619,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_619,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_618)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618)
      | ~ m1_subset_1(E_619,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_619,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_619) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_259,c_256,c_6912])).

tff(c_6977,plain,(
    ! [A_618] :
      ( v1_funct_1(k10_tmap_1(A_618,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_618)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_351,c_6939])).

tff(c_7022,plain,(
    ! [A_618] :
      ( v1_funct_1(k10_tmap_1(A_618,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_618)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_354,c_6977])).

tff(c_7029,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7022])).

tff(c_7032,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2143,c_7029])).

tff(c_7035,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_7032])).

tff(c_7037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7035])).

tff(c_7039,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7022])).

tff(c_577,plain,(
    ! [C_209,D_211,E_210,A_208,B_207] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_208,C_209,D_211)),u1_struct_0(B_207),E_210,k10_tmap_1(A_208,B_207,C_209,D_211,k3_tmap_1(A_208,B_207,k1_tsep_1(A_208,C_209,D_211),C_209,E_210),k3_tmap_1(A_208,B_207,k1_tsep_1(A_208,C_209,D_211),D_211,E_210)))
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208,C_209,D_211)),u1_struct_0(B_207))))
      | ~ v1_funct_2(E_210,u1_struct_0(k1_tsep_1(A_208,C_209,D_211)),u1_struct_0(B_207))
      | ~ v1_funct_1(E_210)
      | ~ m1_pre_topc(D_211,A_208)
      | v2_struct_0(D_211)
      | ~ m1_pre_topc(C_209,A_208)
      | v2_struct_0(C_209)
      | ~ l1_pre_topc(B_207)
      | ~ v2_pre_topc(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

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

tff(c_5438,plain,(
    ! [D_517,E_513,B_516,C_514,A_515] :
      ( k10_tmap_1(A_515,B_516,C_514,D_517,k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),C_514,E_513),k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),D_517,E_513)) = E_513
      | ~ m1_subset_1(k10_tmap_1(A_515,B_516,C_514,D_517,k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),C_514,E_513),k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),D_517,E_513)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_515,C_514,D_517)),u1_struct_0(B_516))))
      | ~ v1_funct_2(k10_tmap_1(A_515,B_516,C_514,D_517,k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),C_514,E_513),k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),D_517,E_513)),u1_struct_0(k1_tsep_1(A_515,C_514,D_517)),u1_struct_0(B_516))
      | ~ v1_funct_1(k10_tmap_1(A_515,B_516,C_514,D_517,k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),C_514,E_513),k3_tmap_1(A_515,B_516,k1_tsep_1(A_515,C_514,D_517),D_517,E_513)))
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_515,C_514,D_517)),u1_struct_0(B_516))))
      | ~ v1_funct_2(E_513,u1_struct_0(k1_tsep_1(A_515,C_514,D_517)),u1_struct_0(B_516))
      | ~ v1_funct_1(E_513)
      | ~ m1_pre_topc(D_517,A_515)
      | v2_struct_0(D_517)
      | ~ m1_pre_topc(C_514,A_515)
      | v2_struct_0(C_514)
      | ~ l1_pre_topc(B_516)
      | ~ v2_pre_topc(B_516)
      | v2_struct_0(B_516)
      | ~ l1_pre_topc(A_515)
      | ~ v2_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_577,c_4])).

tff(c_5453,plain,(
    ! [B_516,E_513] :
      ( k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_513),k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_513)) = E_513
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_3',E_513),k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_513)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_516))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_513),k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_513)),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_516))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_513),k3_tmap_1('#skF_1',B_516,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_513)))
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_516))))
      | ~ v1_funct_2(E_513,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_516))
      | ~ v1_funct_1(E_513)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_516)
      | ~ v2_pre_topc(B_516)
      | v2_struct_0(B_516)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5438])).

tff(c_5462,plain,(
    ! [B_516,E_513] :
      ( k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_3',E_513),k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_4',E_513)) = E_513
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_3',E_513),k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_4',E_513)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_516))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_3',E_513),k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_4',E_513)),u1_struct_0('#skF_1'),u1_struct_0(B_516))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_516,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_3',E_513),k3_tmap_1('#skF_1',B_516,'#skF_1','#skF_4',E_513)))
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_516))))
      | ~ v1_funct_2(E_513,u1_struct_0('#skF_1'),u1_struct_0(B_516))
      | ~ v1_funct_1(E_513)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_516)
      | ~ v2_pre_topc(B_516)
      | v2_struct_0(B_516)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_5453])).

tff(c_10346,plain,(
    ! [B_824,E_825] :
      ( k10_tmap_1('#skF_1',B_824,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_3',E_825),k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_4',E_825)) = E_825
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_824,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_3',E_825),k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_4',E_825)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_824))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_824,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_3',E_825),k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_4',E_825)),u1_struct_0('#skF_1'),u1_struct_0(B_824))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_824,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_3',E_825),k3_tmap_1('#skF_1',B_824,'#skF_1','#skF_4',E_825)))
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_824))))
      | ~ v1_funct_2(E_825,u1_struct_0('#skF_1'),u1_struct_0(B_824))
      | ~ v1_funct_1(E_825)
      | ~ l1_pre_topc(B_824)
      | ~ v2_pre_topc(B_824)
      | v2_struct_0(B_824) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_5462])).

tff(c_10385,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_10346])).

tff(c_10415,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_36,c_7039,c_227,c_332,c_227,c_332,c_227,c_227,c_332,c_10385])).

tff(c_10416,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10415])).

tff(c_10442,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10416])).

tff(c_10446,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1133,c_10442])).

tff(c_10450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_354,c_351,c_10446])).

tff(c_10451,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10416])).

tff(c_10470,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_10451])).

tff(c_10473,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_514,c_10470])).

tff(c_10476,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_357,c_354,c_351,c_262,c_259,c_256,c_10473])).

tff(c_10478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10476])).

tff(c_10479,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10451])).

tff(c_34,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_63,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_10486,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10479,c_63])).

tff(c_10616,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_10486])).

tff(c_10619,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_10616])).

tff(c_10621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_10619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.35  % Computer   : n006.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 20:02:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.30/4.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.30/4.92  
% 12.30/4.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.30/4.93  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.30/4.93  
% 12.30/4.93  %Foreground sorts:
% 12.30/4.93  
% 12.30/4.93  
% 12.30/4.93  %Background operators:
% 12.30/4.93  
% 12.30/4.93  
% 12.30/4.93  %Foreground operators:
% 12.30/4.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.30/4.93  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.30/4.93  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 12.30/4.93  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.30/4.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.30/4.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.30/4.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.30/4.93  tff('#skF_5', type, '#skF_5': $i).
% 12.30/4.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.30/4.93  tff('#skF_2', type, '#skF_2': $i).
% 12.30/4.93  tff('#skF_3', type, '#skF_3': $i).
% 12.30/4.93  tff('#skF_1', type, '#skF_1': $i).
% 12.30/4.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.30/4.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.30/4.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.30/4.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.30/4.93  tff('#skF_4', type, '#skF_4': $i).
% 12.30/4.93  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 12.30/4.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.30/4.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.30/4.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.30/4.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.30/4.93  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.30/4.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.30/4.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.30/4.93  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 12.30/4.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.30/4.93  
% 12.45/4.96  tff(f_285, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_tmap_1)).
% 12.45/4.96  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.45/4.96  tff(f_75, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 12.45/4.96  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 12.45/4.96  tff(f_246, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.45/4.96  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 12.45/4.96  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 12.45/4.96  tff(f_206, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 12.45/4.96  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 12.45/4.96  tff(f_242, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 12.45/4.96  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 12.45/4.96  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.45/4.96  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_84, plain, (![D_138, C_140, A_141, F_142, B_139]: (r1_funct_2(A_141, B_139, C_140, D_138, F_142, F_142) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_140, D_138))) | ~v1_funct_2(F_142, C_140, D_138) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))) | ~v1_funct_2(F_142, A_141, B_139) | ~v1_funct_1(F_142) | v1_xboole_0(D_138) | v1_xboole_0(B_139))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.45/4.96  tff(c_86, plain, (![A_141, B_139]: (r1_funct_2(A_141, B_139, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))) | ~v1_funct_2('#skF_5', A_141, B_139) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_139))), inference(resolution, [status(thm)], [c_36, c_84])).
% 12.45/4.96  tff(c_89, plain, (![A_141, B_139]: (r1_funct_2(A_141, B_139, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))) | ~v1_funct_2('#skF_5', A_141, B_139) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_86])).
% 12.45/4.96  tff(c_90, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_89])).
% 12.45/4.96  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.45/4.96  tff(c_93, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_8])).
% 12.45/4.96  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_93])).
% 12.45/4.96  tff(c_99, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_96])).
% 12.45/4.96  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 12.45/4.96  tff(c_105, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_89])).
% 12.45/4.96  tff(c_104, plain, (![A_141, B_139]: (r1_funct_2(A_141, B_139, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))) | ~v1_funct_2('#skF_5', A_141, B_139) | v1_xboole_0(B_139))), inference(splitRight, [status(thm)], [c_89])).
% 12.45/4.96  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_32, plain, (![A_101]: (m1_pre_topc(A_101, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_246])).
% 12.45/4.96  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_163, plain, (![D_179, B_178, A_176, C_177, E_175]: (k3_tmap_1(A_176, B_178, C_177, D_179, E_175)=k2_partfun1(u1_struct_0(C_177), u1_struct_0(B_178), E_175, u1_struct_0(D_179)) | ~m1_pre_topc(D_179, C_177) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_177), u1_struct_0(B_178)))) | ~v1_funct_2(E_175, u1_struct_0(C_177), u1_struct_0(B_178)) | ~v1_funct_1(E_175) | ~m1_pre_topc(D_179, A_176) | ~m1_pre_topc(C_177, A_176) | ~l1_pre_topc(B_178) | ~v2_pre_topc(B_178) | v2_struct_0(B_178) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.45/4.96  tff(c_167, plain, (![A_176, D_179]: (k3_tmap_1(A_176, '#skF_2', '#skF_1', D_179, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_179)) | ~m1_pre_topc(D_179, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_179, A_176) | ~m1_pre_topc('#skF_1', A_176) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_36, c_163])).
% 12.45/4.96  tff(c_171, plain, (![A_176, D_179]: (k3_tmap_1(A_176, '#skF_2', '#skF_1', D_179, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_179)) | ~m1_pre_topc(D_179, '#skF_1') | ~m1_pre_topc(D_179, A_176) | ~m1_pre_topc('#skF_1', A_176) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_167])).
% 12.45/4.96  tff(c_173, plain, (![A_180, D_181]: (k3_tmap_1(A_180, '#skF_2', '#skF_1', D_181, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181)) | ~m1_pre_topc(D_181, '#skF_1') | ~m1_pre_topc(D_181, A_180) | ~m1_pre_topc('#skF_1', A_180) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(negUnitSimplification, [status(thm)], [c_56, c_171])).
% 12.45/4.96  tff(c_177, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_173])).
% 12.45/4.96  tff(c_183, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_177])).
% 12.45/4.96  tff(c_184, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_183])).
% 12.45/4.96  tff(c_189, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_184])).
% 12.45/4.96  tff(c_192, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_189])).
% 12.45/4.96  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_192])).
% 12.45/4.96  tff(c_198, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 12.45/4.96  tff(c_197, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_184])).
% 12.45/4.96  tff(c_123, plain, (![A_158, B_159, C_160, D_161]: (k2_partfun1(u1_struct_0(A_158), u1_struct_0(B_159), C_160, u1_struct_0(D_161))=k2_tmap_1(A_158, B_159, C_160, D_161) | ~m1_pre_topc(D_161, A_158) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), u1_struct_0(B_159)))) | ~v1_funct_2(C_160, u1_struct_0(A_158), u1_struct_0(B_159)) | ~v1_funct_1(C_160) | ~l1_pre_topc(B_159) | ~v2_pre_topc(B_159) | v2_struct_0(B_159) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.45/4.96  tff(c_125, plain, (![D_161]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_161))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_161) | ~m1_pre_topc(D_161, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_123])).
% 12.45/4.96  tff(c_128, plain, (![D_161]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_161))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_161) | ~m1_pre_topc(D_161, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_40, c_38, c_125])).
% 12.45/4.96  tff(c_129, plain, (![D_161]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_161))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_161) | ~m1_pre_topc(D_161, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_128])).
% 12.45/4.96  tff(c_325, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_197, c_129])).
% 12.45/4.96  tff(c_332, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_325])).
% 12.45/4.96  tff(c_115, plain, (![E_155, C_152, A_154, D_151, B_153]: (v1_funct_1(k3_tmap_1(A_154, B_153, C_152, D_151, E_155)) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_152), u1_struct_0(B_153)))) | ~v1_funct_2(E_155, u1_struct_0(C_152), u1_struct_0(B_153)) | ~v1_funct_1(E_155) | ~m1_pre_topc(D_151, A_154) | ~m1_pre_topc(C_152, A_154) | ~l1_pre_topc(B_153) | ~v2_pre_topc(B_153) | v2_struct_0(B_153) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.45/4.96  tff(c_117, plain, (![A_154, D_151]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_151, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_151, A_154) | ~m1_pre_topc('#skF_1', A_154) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_36, c_115])).
% 12.45/4.96  tff(c_120, plain, (![A_154, D_151]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_151, '#skF_5')) | ~m1_pre_topc(D_151, A_154) | ~m1_pre_topc('#skF_1', A_154) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_117])).
% 12.45/4.96  tff(c_121, plain, (![A_154, D_151]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_151, '#skF_5')) | ~m1_pre_topc(D_151, A_154) | ~m1_pre_topc('#skF_1', A_154) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(negUnitSimplification, [status(thm)], [c_56, c_120])).
% 12.45/4.96  tff(c_346, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_121])).
% 12.45/4.96  tff(c_356, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_198, c_48, c_346])).
% 12.45/4.96  tff(c_357, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_356])).
% 12.45/4.96  tff(c_139, plain, (![A_166, E_167, B_165, C_164, D_163]: (v1_funct_2(k3_tmap_1(A_166, B_165, C_164, D_163, E_167), u1_struct_0(D_163), u1_struct_0(B_165)) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_164), u1_struct_0(B_165)))) | ~v1_funct_2(E_167, u1_struct_0(C_164), u1_struct_0(B_165)) | ~v1_funct_1(E_167) | ~m1_pre_topc(D_163, A_166) | ~m1_pre_topc(C_164, A_166) | ~l1_pre_topc(B_165) | ~v2_pre_topc(B_165) | v2_struct_0(B_165) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.45/4.96  tff(c_141, plain, (![A_166, D_163]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_163, '#skF_5'), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_163, A_166) | ~m1_pre_topc('#skF_1', A_166) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_36, c_139])).
% 12.45/4.96  tff(c_144, plain, (![A_166, D_163]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_163, '#skF_5'), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_163, A_166) | ~m1_pre_topc('#skF_1', A_166) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_141])).
% 12.45/4.96  tff(c_145, plain, (![A_166, D_163]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_163, '#skF_5'), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_163, A_166) | ~m1_pre_topc('#skF_1', A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(negUnitSimplification, [status(thm)], [c_56, c_144])).
% 12.45/4.96  tff(c_343, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_145])).
% 12.45/4.96  tff(c_353, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_198, c_48, c_343])).
% 12.45/4.96  tff(c_354, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_353])).
% 12.45/4.96  tff(c_24, plain, (![B_66, A_65, C_67, D_68, E_69]: (m1_subset_1(k3_tmap_1(A_65, B_66, C_67, D_68, E_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68), u1_struct_0(B_66)))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67), u1_struct_0(B_66)))) | ~v1_funct_2(E_69, u1_struct_0(C_67), u1_struct_0(B_66)) | ~v1_funct_1(E_69) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc(C_67, A_65) | ~l1_pre_topc(B_66) | ~v2_pre_topc(B_66) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.45/4.96  tff(c_340, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_24])).
% 12.45/4.96  tff(c_350, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_198, c_48, c_40, c_38, c_36, c_340])).
% 12.45/4.96  tff(c_351, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_350])).
% 12.45/4.96  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_179, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_173])).
% 12.45/4.96  tff(c_187, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_179])).
% 12.45/4.96  tff(c_188, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_187])).
% 12.45/4.96  tff(c_199, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_188])).
% 12.45/4.96  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_199])).
% 12.45/4.96  tff(c_208, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_188])).
% 12.45/4.96  tff(c_220, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_208, c_129])).
% 12.45/4.96  tff(c_227, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_220])).
% 12.45/4.96  tff(c_251, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_121])).
% 12.45/4.96  tff(c_261, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_198, c_44, c_251])).
% 12.45/4.96  tff(c_262, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_261])).
% 12.45/4.96  tff(c_248, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_145])).
% 12.45/4.96  tff(c_258, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_198, c_44, c_248])).
% 12.45/4.96  tff(c_259, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_258])).
% 12.45/4.96  tff(c_245, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_24])).
% 12.45/4.96  tff(c_255, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_198, c_44, c_40, c_38, c_36, c_245])).
% 12.45/4.96  tff(c_256, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_255])).
% 12.45/4.96  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_42, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_487, plain, (![A_195, C_194, B_196, E_199, D_198, F_197]: (m1_subset_1(k10_tmap_1(A_195, B_196, C_194, D_198, E_199, F_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_195, C_194, D_198)), u1_struct_0(B_196)))) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0(D_198), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0(C_194), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | ~m1_pre_topc(D_198, A_195) | v2_struct_0(D_198) | ~m1_pre_topc(C_194, A_195) | v2_struct_0(C_194) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.45/4.96  tff(c_504, plain, (![B_196, E_199, F_197]: (m1_subset_1(k10_tmap_1('#skF_1', B_196, '#skF_3', '#skF_4', E_199, F_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_196)))) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0('#skF_4'), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0('#skF_3'), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_487])).
% 12.45/4.96  tff(c_513, plain, (![B_196, E_199, F_197]: (m1_subset_1(k10_tmap_1('#skF_1', B_196, '#skF_3', '#skF_4', E_199, F_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_196)))) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0('#skF_4'), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0('#skF_3'), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_504])).
% 12.45/4.96  tff(c_514, plain, (![B_196, E_199, F_197]: (m1_subset_1(k10_tmap_1('#skF_1', B_196, '#skF_3', '#skF_4', E_199, F_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_196)))) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0('#skF_4'), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0('#skF_3'), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_513])).
% 12.45/4.96  tff(c_359, plain, (![D_192, E_193, C_188, B_190, F_191, A_189]: (v1_funct_2(k10_tmap_1(A_189, B_190, C_188, D_192, E_193, F_191), u1_struct_0(k1_tsep_1(A_189, C_188, D_192)), u1_struct_0(B_190)) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_192), u1_struct_0(B_190)))) | ~v1_funct_2(F_191, u1_struct_0(D_192), u1_struct_0(B_190)) | ~v1_funct_1(F_191) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0(B_190)))) | ~v1_funct_2(E_193, u1_struct_0(C_188), u1_struct_0(B_190)) | ~v1_funct_1(E_193) | ~m1_pre_topc(D_192, A_189) | v2_struct_0(D_192) | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.45/4.96  tff(c_362, plain, (![B_190, E_193, F_191]: (v1_funct_2(k10_tmap_1('#skF_1', B_190, '#skF_3', '#skF_4', E_193, F_191), u1_struct_0('#skF_1'), u1_struct_0(B_190)) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_190)))) | ~v1_funct_2(F_191, u1_struct_0('#skF_4'), u1_struct_0(B_190)) | ~v1_funct_1(F_191) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_190)))) | ~v1_funct_2(E_193, u1_struct_0('#skF_3'), u1_struct_0(B_190)) | ~v1_funct_1(E_193) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_359])).
% 12.45/4.96  tff(c_364, plain, (![B_190, E_193, F_191]: (v1_funct_2(k10_tmap_1('#skF_1', B_190, '#skF_3', '#skF_4', E_193, F_191), u1_struct_0('#skF_1'), u1_struct_0(B_190)) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_190)))) | ~v1_funct_2(F_191, u1_struct_0('#skF_4'), u1_struct_0(B_190)) | ~v1_funct_1(F_191) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_190)))) | ~v1_funct_2(E_193, u1_struct_0('#skF_3'), u1_struct_0(B_190)) | ~v1_funct_1(E_193) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_362])).
% 12.45/4.96  tff(c_1103, plain, (![B_246, E_247, F_248]: (v1_funct_2(k10_tmap_1('#skF_1', B_246, '#skF_3', '#skF_4', E_247, F_248), u1_struct_0('#skF_1'), u1_struct_0(B_246)) | ~m1_subset_1(F_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_246)))) | ~v1_funct_2(F_248, u1_struct_0('#skF_4'), u1_struct_0(B_246)) | ~v1_funct_1(F_248) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_246)))) | ~v1_funct_2(E_247, u1_struct_0('#skF_3'), u1_struct_0(B_246)) | ~v1_funct_1(E_247) | ~l1_pre_topc(B_246) | ~v2_pre_topc(B_246) | v2_struct_0(B_246))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_364])).
% 12.45/4.96  tff(c_1114, plain, (![E_247]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_247, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_247) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_256, c_1103])).
% 12.45/4.96  tff(c_1132, plain, (![E_247]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_247, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_247) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_262, c_259, c_1114])).
% 12.45/4.96  tff(c_1133, plain, (![E_247]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_247, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_247))), inference(negUnitSimplification, [status(thm)], [c_56, c_1132])).
% 12.45/4.96  tff(c_22, plain, (![F_64, D_62, A_59, C_61, E_63, B_60]: (v1_funct_1(k10_tmap_1(A_59, B_60, C_61, D_62, E_63, F_64)) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62), u1_struct_0(B_60)))) | ~v1_funct_2(F_64, u1_struct_0(D_62), u1_struct_0(B_60)) | ~v1_funct_1(F_64) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_60)))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0(B_60)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_62, A_59) | v2_struct_0(D_62) | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.45/4.96  tff(c_265, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_256, c_22])).
% 12.45/4.96  tff(c_280, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_262, c_259, c_265])).
% 12.45/4.96  tff(c_2047, plain, (![A_277, C_278, E_279]: (v1_funct_1(k10_tmap_1(A_277, '#skF_2', C_278, '#skF_4', E_279, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_279, u1_struct_0(C_278), u1_struct_0('#skF_2')) | ~v1_funct_1(E_279) | ~m1_pre_topc('#skF_4', A_277) | ~m1_pre_topc(C_278, A_277) | v2_struct_0(C_278) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(negUnitSimplification, [status(thm)], [c_56, c_46, c_280])).
% 12.45/4.96  tff(c_2087, plain, (![A_277]: (v1_funct_1(k10_tmap_1(A_277, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', A_277) | ~m1_pre_topc('#skF_3', A_277) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(resolution, [status(thm)], [c_351, c_2047])).
% 12.45/4.96  tff(c_2142, plain, (![A_277]: (v1_funct_1(k10_tmap_1(A_277, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_277) | ~m1_pre_topc('#skF_3', A_277) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_354, c_2087])).
% 12.45/4.96  tff(c_2143, plain, (![A_277]: (v1_funct_1(k10_tmap_1(A_277, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_277) | ~m1_pre_topc('#skF_3', A_277) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(negUnitSimplification, [status(thm)], [c_50, c_2142])).
% 12.45/4.96  tff(c_1443, plain, (![B_257, E_258, F_259]: (m1_subset_1(k10_tmap_1('#skF_1', B_257, '#skF_3', '#skF_4', E_258, F_259), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_257)))) | ~m1_subset_1(F_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_257)))) | ~v1_funct_2(F_259, u1_struct_0('#skF_4'), u1_struct_0(B_257)) | ~v1_funct_1(F_259) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_257)))) | ~v1_funct_2(E_258, u1_struct_0('#skF_3'), u1_struct_0(B_257)) | ~v1_funct_1(E_258) | ~l1_pre_topc(B_257) | ~v2_pre_topc(B_257) | v2_struct_0(B_257))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_513])).
% 12.45/4.96  tff(c_231, plain, (![C_182, F_185, D_186, A_183, B_184, E_187]: (v1_funct_1(k10_tmap_1(A_183, B_184, C_182, D_186, E_187, F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_186), u1_struct_0(B_184)))) | ~v1_funct_2(F_185, u1_struct_0(D_186), u1_struct_0(B_184)) | ~v1_funct_1(F_185) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182), u1_struct_0(B_184)))) | ~v1_funct_2(E_187, u1_struct_0(C_182), u1_struct_0(B_184)) | ~v1_funct_1(E_187) | ~m1_pre_topc(D_186, A_183) | v2_struct_0(D_186) | ~m1_pre_topc(C_182, A_183) | v2_struct_0(C_182) | ~l1_pre_topc(B_184) | ~v2_pre_topc(B_184) | v2_struct_0(B_184) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.45/4.96  tff(c_235, plain, (![A_183, C_182, E_187]: (v1_funct_1(k10_tmap_1(A_183, '#skF_2', C_182, '#skF_1', E_187, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_187, u1_struct_0(C_182), u1_struct_0('#skF_2')) | ~v1_funct_1(E_187) | ~m1_pre_topc('#skF_1', A_183) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_182, A_183) | v2_struct_0(C_182) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(resolution, [status(thm)], [c_36, c_231])).
% 12.45/4.96  tff(c_239, plain, (![A_183, C_182, E_187]: (v1_funct_1(k10_tmap_1(A_183, '#skF_2', C_182, '#skF_1', E_187, '#skF_5')) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_187, u1_struct_0(C_182), u1_struct_0('#skF_2')) | ~v1_funct_1(E_187) | ~m1_pre_topc('#skF_1', A_183) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_182, A_183) | v2_struct_0(C_182) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_235])).
% 12.45/4.96  tff(c_240, plain, (![A_183, C_182, E_187]: (v1_funct_1(k10_tmap_1(A_183, '#skF_2', C_182, '#skF_1', E_187, '#skF_5')) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_187, u1_struct_0(C_182), u1_struct_0('#skF_2')) | ~v1_funct_1(E_187) | ~m1_pre_topc('#skF_1', A_183) | ~m1_pre_topc(C_182, A_183) | v2_struct_0(C_182) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_239])).
% 12.45/4.96  tff(c_1446, plain, (![A_183, E_258, F_259]: (v1_funct_1(k10_tmap_1(A_183, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259)) | ~m1_pre_topc('#skF_1', A_183) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183) | ~m1_subset_1(F_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_259, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_259) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_258, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_258) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1443, c_240])).
% 12.45/4.96  tff(c_1463, plain, (![A_183, E_258, F_259]: (v1_funct_1(k10_tmap_1(A_183, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_258, F_259)) | ~m1_pre_topc('#skF_1', A_183) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183) | ~m1_subset_1(F_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_259, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_259) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_258, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_258) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1446])).
% 12.45/4.96  tff(c_6910, plain, (![A_609, E_610, F_611]: (v1_funct_1(k10_tmap_1(A_609, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_610, F_611), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_610, F_611), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_610, F_611)) | ~m1_pre_topc('#skF_1', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609) | ~m1_subset_1(F_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_611, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_611) | ~m1_subset_1(E_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_610, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_610))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_1463])).
% 12.45/4.96  tff(c_6912, plain, (![A_609, E_247]: (v1_funct_1(k10_tmap_1(A_609, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_247, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_247, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_247))), inference(resolution, [status(thm)], [c_1133, c_6910])).
% 12.45/4.96  tff(c_6939, plain, (![A_618, E_619]: (v1_funct_1(k10_tmap_1(A_618, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_619, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_619, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_618) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618) | ~m1_subset_1(E_619, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_619, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_619))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_259, c_256, c_6912])).
% 12.45/4.96  tff(c_6977, plain, (![A_618]: (v1_funct_1(k10_tmap_1(A_618, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_618) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_351, c_6939])).
% 12.45/4.96  tff(c_7022, plain, (![A_618]: (v1_funct_1(k10_tmap_1(A_618, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_618) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_354, c_6977])).
% 12.45/4.96  tff(c_7029, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_7022])).
% 12.45/4.96  tff(c_7032, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2143, c_7029])).
% 12.45/4.96  tff(c_7035, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_7032])).
% 12.45/4.96  tff(c_7037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_7035])).
% 12.45/4.96  tff(c_7039, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_7022])).
% 12.45/4.96  tff(c_577, plain, (![C_209, D_211, E_210, A_208, B_207]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_208, C_209, D_211)), u1_struct_0(B_207), E_210, k10_tmap_1(A_208, B_207, C_209, D_211, k3_tmap_1(A_208, B_207, k1_tsep_1(A_208, C_209, D_211), C_209, E_210), k3_tmap_1(A_208, B_207, k1_tsep_1(A_208, C_209, D_211), D_211, E_210))) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208, C_209, D_211)), u1_struct_0(B_207)))) | ~v1_funct_2(E_210, u1_struct_0(k1_tsep_1(A_208, C_209, D_211)), u1_struct_0(B_207)) | ~v1_funct_1(E_210) | ~m1_pre_topc(D_211, A_208) | v2_struct_0(D_211) | ~m1_pre_topc(C_209, A_208) | v2_struct_0(C_209) | ~l1_pre_topc(B_207) | ~v2_pre_topc(B_207) | v2_struct_0(B_207) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_242])).
% 12.45/4.96  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.45/4.96  tff(c_5438, plain, (![D_517, E_513, B_516, C_514, A_515]: (k10_tmap_1(A_515, B_516, C_514, D_517, k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), C_514, E_513), k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), D_517, E_513))=E_513 | ~m1_subset_1(k10_tmap_1(A_515, B_516, C_514, D_517, k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), C_514, E_513), k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), D_517, E_513)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_515, C_514, D_517)), u1_struct_0(B_516)))) | ~v1_funct_2(k10_tmap_1(A_515, B_516, C_514, D_517, k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), C_514, E_513), k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), D_517, E_513)), u1_struct_0(k1_tsep_1(A_515, C_514, D_517)), u1_struct_0(B_516)) | ~v1_funct_1(k10_tmap_1(A_515, B_516, C_514, D_517, k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), C_514, E_513), k3_tmap_1(A_515, B_516, k1_tsep_1(A_515, C_514, D_517), D_517, E_513))) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_515, C_514, D_517)), u1_struct_0(B_516)))) | ~v1_funct_2(E_513, u1_struct_0(k1_tsep_1(A_515, C_514, D_517)), u1_struct_0(B_516)) | ~v1_funct_1(E_513) | ~m1_pre_topc(D_517, A_515) | v2_struct_0(D_517) | ~m1_pre_topc(C_514, A_515) | v2_struct_0(C_514) | ~l1_pre_topc(B_516) | ~v2_pre_topc(B_516) | v2_struct_0(B_516) | ~l1_pre_topc(A_515) | ~v2_pre_topc(A_515) | v2_struct_0(A_515))), inference(resolution, [status(thm)], [c_577, c_4])).
% 12.45/4.96  tff(c_5453, plain, (![B_516, E_513]: (k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_513))=E_513 | ~m1_subset_1(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_513)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_516)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_513)), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_516)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_513))) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_516)))) | ~v1_funct_2(E_513, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_516)) | ~v1_funct_1(E_513) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_516) | ~v2_pre_topc(B_516) | v2_struct_0(B_516) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5438])).
% 12.45/4.96  tff(c_5462, plain, (![B_516, E_513]: (k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_4', E_513))=E_513 | ~m1_subset_1(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_4', E_513)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_516)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_4', E_513)), u1_struct_0('#skF_1'), u1_struct_0(B_516)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_516, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_3', E_513), k3_tmap_1('#skF_1', B_516, '#skF_1', '#skF_4', E_513))) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_516)))) | ~v1_funct_2(E_513, u1_struct_0('#skF_1'), u1_struct_0(B_516)) | ~v1_funct_1(E_513) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_516) | ~v2_pre_topc(B_516) | v2_struct_0(B_516) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_5453])).
% 12.45/4.96  tff(c_10346, plain, (![B_824, E_825]: (k10_tmap_1('#skF_1', B_824, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_3', E_825), k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_4', E_825))=E_825 | ~m1_subset_1(k10_tmap_1('#skF_1', B_824, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_3', E_825), k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_4', E_825)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_824)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_824, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_3', E_825), k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_4', E_825)), u1_struct_0('#skF_1'), u1_struct_0(B_824)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_824, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_3', E_825), k3_tmap_1('#skF_1', B_824, '#skF_1', '#skF_4', E_825))) | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_824)))) | ~v1_funct_2(E_825, u1_struct_0('#skF_1'), u1_struct_0(B_824)) | ~v1_funct_1(E_825) | ~l1_pre_topc(B_824) | ~v2_pre_topc(B_824) | v2_struct_0(B_824))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_5462])).
% 12.45/4.96  tff(c_10385, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_332, c_10346])).
% 12.45/4.96  tff(c_10415, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_36, c_7039, c_227, c_332, c_227, c_332, c_227, c_227, c_332, c_10385])).
% 12.45/4.96  tff(c_10416, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_10415])).
% 12.45/4.96  tff(c_10442, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_10416])).
% 12.45/4.96  tff(c_10446, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_1133, c_10442])).
% 12.45/4.96  tff(c_10450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_354, c_351, c_10446])).
% 12.45/4.96  tff(c_10451, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_10416])).
% 12.45/4.96  tff(c_10470, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_10451])).
% 12.45/4.96  tff(c_10473, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_514, c_10470])).
% 12.45/4.96  tff(c_10476, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_357, c_354, c_351, c_262, c_259, c_256, c_10473])).
% 12.45/4.96  tff(c_10478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_10476])).
% 12.45/4.96  tff(c_10479, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_10451])).
% 12.45/4.96  tff(c_34, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_285])).
% 12.45/4.96  tff(c_63, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 12.45/4.96  tff(c_10486, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10479, c_63])).
% 12.45/4.96  tff(c_10616, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_104, c_10486])).
% 12.45/4.96  tff(c_10619, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_10616])).
% 12.45/4.96  tff(c_10621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_10619])).
% 12.45/4.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.45/4.96  
% 12.45/4.96  Inference rules
% 12.45/4.96  ----------------------
% 12.45/4.96  #Ref     : 0
% 12.45/4.96  #Sup     : 1967
% 12.45/4.96  #Fact    : 0
% 12.45/4.96  #Define  : 0
% 12.45/4.96  #Split   : 24
% 12.45/4.96  #Chain   : 0
% 12.45/4.96  #Close   : 0
% 12.45/4.96  
% 12.45/4.96  Ordering : KBO
% 12.45/4.96  
% 12.45/4.96  Simplification rules
% 12.45/4.96  ----------------------
% 12.45/4.96  #Subsume      : 933
% 12.45/4.96  #Demod        : 5758
% 12.45/4.96  #Tautology    : 348
% 12.45/4.96  #SimpNegUnit  : 1042
% 12.45/4.96  #BackRed      : 45
% 12.45/4.96  
% 12.45/4.96  #Partial instantiations: 0
% 12.45/4.96  #Strategies tried      : 1
% 12.45/4.96  
% 12.45/4.96  Timing (in seconds)
% 12.45/4.96  ----------------------
% 12.45/4.96  Preprocessing        : 0.38
% 12.45/4.96  Parsing              : 0.21
% 12.45/4.96  CNF conversion       : 0.04
% 12.45/4.96  Main loop            : 3.77
% 12.45/4.96  Inferencing          : 1.10
% 12.45/4.96  Reduction            : 1.42
% 12.45/4.96  Demodulation         : 1.12
% 12.45/4.96  BG Simplification    : 0.08
% 12.45/4.96  Subsumption          : 1.00
% 12.45/4.96  Abstraction          : 0.15
% 12.45/4.96  MUC search           : 0.00
% 12.45/4.96  Cooper               : 0.00
% 12.45/4.96  Total                : 4.22
% 12.45/4.96  Index Insertion      : 0.00
% 12.45/4.96  Index Deletion       : 0.00
% 12.45/4.96  Index Matching       : 0.00
% 12.45/4.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
