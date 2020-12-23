%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 970 expanded)
%              Number of leaves         :   29 ( 398 expanded)
%              Depth                    :   21
%              Number of atoms          :  404 (7307 expanded)
%              Number of equality atoms :   17 ( 201 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_220,negated_conjecture,(
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
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
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

tff(f_130,axiom,(
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

tff(f_181,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_26,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_16,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_108,plain,(
    ! [C_182,D_179,E_178,A_180,B_181] :
      ( k3_tmap_1(A_180,B_181,C_182,D_179,E_178) = k2_partfun1(u1_struct_0(C_182),u1_struct_0(B_181),E_178,u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,C_182)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182),u1_struct_0(B_181))))
      | ~ v1_funct_2(E_178,u1_struct_0(C_182),u1_struct_0(B_181))
      | ~ v1_funct_1(E_178)
      | ~ m1_pre_topc(D_179,A_180)
      | ~ m1_pre_topc(C_182,A_180)
      | ~ l1_pre_topc(B_181)
      | ~ v2_pre_topc(B_181)
      | v2_struct_0(B_181)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_112,plain,(
    ! [A_180,D_179] :
      ( k3_tmap_1(A_180,'#skF_2','#skF_1',D_179,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_179,A_180)
      | ~ m1_pre_topc('#skF_1',A_180)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_24,c_108])).

tff(c_116,plain,(
    ! [A_180,D_179] :
      ( k3_tmap_1(A_180,'#skF_2','#skF_1',D_179,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_179))
      | ~ m1_pre_topc(D_179,'#skF_1')
      | ~ m1_pre_topc(D_179,A_180)
      | ~ m1_pre_topc('#skF_1',A_180)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_112])).

tff(c_118,plain,(
    ! [A_183,D_184] :
      ( k3_tmap_1(A_183,'#skF_2','#skF_1',D_184,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_184))
      | ~ m1_pre_topc(D_184,'#skF_1')
      | ~ m1_pre_topc(D_184,A_183)
      | ~ m1_pre_topc('#skF_1',A_183)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_116])).

tff(c_122,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_130,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_30,c_122])).

tff(c_131,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_130])).

tff(c_140,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_144])).

tff(c_150,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_149,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_71,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k2_partfun1(u1_struct_0(A_161),u1_struct_0(B_162),C_163,u1_struct_0(D_164)) = k2_tmap_1(A_161,B_162,C_163,D_164)
      | ~ m1_pre_topc(D_164,A_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_161),u1_struct_0(B_162))))
      | ~ v1_funct_2(C_163,u1_struct_0(A_161),u1_struct_0(B_162))
      | ~ v1_funct_1(C_163)
      | ~ l1_pre_topc(B_162)
      | ~ v2_pre_topc(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    ! [D_164] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_164)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_164)
      | ~ m1_pre_topc(D_164,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_76,plain,(
    ! [D_164] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_164)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_164)
      | ~ m1_pre_topc(D_164,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_28,c_26,c_73])).

tff(c_77,plain,(
    ! [D_164] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_164)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_164)
      | ~ m1_pre_topc(D_164,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_76])).

tff(c_160,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_77])).

tff(c_167,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_160])).

tff(c_63,plain,(
    ! [B_155,D_157,A_154,C_156,E_158] :
      ( v1_funct_1(k3_tmap_1(A_154,B_155,C_156,D_157,E_158))
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_156),u1_struct_0(B_155))))
      | ~ v1_funct_2(E_158,u1_struct_0(C_156),u1_struct_0(B_155))
      | ~ v1_funct_1(E_158)
      | ~ m1_pre_topc(D_157,A_154)
      | ~ m1_pre_topc(C_156,A_154)
      | ~ l1_pre_topc(B_155)
      | ~ v2_pre_topc(B_155)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_65,plain,(
    ! [A_154,D_157] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_157,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_68,plain,(
    ! [A_154,D_157] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ m1_pre_topc(D_157,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_65])).

tff(c_69,plain,(
    ! [A_154,D_157] :
      ( v1_funct_1(k3_tmap_1(A_154,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ m1_pre_topc(D_157,A_154)
      | ~ m1_pre_topc('#skF_1',A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_68])).

tff(c_181,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_69])).

tff(c_191,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_150,c_30,c_181])).

tff(c_192,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_191])).

tff(c_87,plain,(
    ! [D_169,E_170,A_166,B_167,C_168] :
      ( v1_funct_2(k3_tmap_1(A_166,B_167,C_168,D_169,E_170),u1_struct_0(D_169),u1_struct_0(B_167))
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168),u1_struct_0(B_167))))
      | ~ v1_funct_2(E_170,u1_struct_0(C_168),u1_struct_0(B_167))
      | ~ v1_funct_1(E_170)
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_pre_topc(C_168,A_166)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_89,plain,(
    ! [A_166,D_169] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_92,plain,(
    ! [A_166,D_169] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_89])).

tff(c_93,plain,(
    ! [A_166,D_169] :
      ( v1_funct_2(k3_tmap_1(A_166,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_pre_topc('#skF_1',A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_92])).

tff(c_178,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_93])).

tff(c_188,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_150,c_30,c_178])).

tff(c_189,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_188])).

tff(c_10,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( m1_subset_1(k3_tmap_1(A_51,B_52,C_53,D_54,E_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54),u1_struct_0(B_52))))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_175,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_167,c_10])).

tff(c_185,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_150,c_30,c_28,c_26,c_24,c_175])).

tff(c_186,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_185])).

tff(c_95,plain,(
    ! [E_177,B_174,D_176,C_175,A_173] :
      ( m1_subset_1(k3_tmap_1(A_173,B_174,C_175,D_176,E_177),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_176),u1_struct_0(B_174))))
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_175),u1_struct_0(B_174))))
      | ~ v1_funct_2(E_177,u1_struct_0(C_175),u1_struct_0(B_174))
      | ~ v1_funct_1(E_177)
      | ~ m1_pre_topc(D_176,A_173)
      | ~ m1_pre_topc(C_175,A_173)
      | ~ l1_pre_topc(B_174)
      | ~ v2_pre_topc(B_174)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_292,plain,(
    ! [B_194,E_193,D_195,A_192,C_191] :
      ( r2_funct_2(u1_struct_0(D_195),u1_struct_0(B_194),k3_tmap_1(A_192,B_194,C_191,D_195,E_193),k3_tmap_1(A_192,B_194,C_191,D_195,E_193))
      | ~ v1_funct_2(k3_tmap_1(A_192,B_194,C_191,D_195,E_193),u1_struct_0(D_195),u1_struct_0(B_194))
      | ~ v1_funct_1(k3_tmap_1(A_192,B_194,C_191,D_195,E_193))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191),u1_struct_0(B_194))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_191),u1_struct_0(B_194))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc(D_195,A_192)
      | ~ m1_pre_topc(C_191,A_192)
      | ~ l1_pre_topc(B_194)
      | ~ v2_pre_topc(B_194)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_303,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
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
    inference(superposition,[status(thm),theory(equality)],[c_167,c_292])).

tff(c_316,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_150,c_30,c_28,c_26,c_24,c_192,c_167,c_189,c_167,c_167,c_303])).

tff(c_317,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_316])).

tff(c_18,plain,(
    ! [A_57,C_105,B_89,E_117,D_113,F_119] :
      ( r2_funct_2(u1_struct_0(D_113),u1_struct_0(B_89),k3_tmap_1(A_57,B_89,C_105,D_113,F_119),k2_tmap_1(A_57,B_89,E_117,D_113))
      | ~ m1_pre_topc(D_113,C_105)
      | ~ r2_funct_2(u1_struct_0(C_105),u1_struct_0(B_89),F_119,k2_tmap_1(A_57,B_89,E_117,C_105))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_105),u1_struct_0(B_89))))
      | ~ v1_funct_2(F_119,u1_struct_0(C_105),u1_struct_0(B_89))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57),u1_struct_0(B_89))))
      | ~ v1_funct_2(E_117,u1_struct_0(A_57),u1_struct_0(B_89))
      | ~ v1_funct_1(E_117)
      | ~ m1_pre_topc(D_113,A_57)
      | v2_struct_0(D_113)
      | ~ m1_pre_topc(C_105,A_57)
      | v2_struct_0(C_105)
      | ~ l1_pre_topc(B_89)
      | ~ v2_pre_topc(B_89)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_354,plain,(
    ! [D_113] :
      ( r2_funct_2(u1_struct_0(D_113),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_113,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_113))
      | ~ m1_pre_topc(D_113,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_113,'#skF_1')
      | v2_struct_0(D_113)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_317,c_18])).

tff(c_359,plain,(
    ! [D_113] :
      ( r2_funct_2(u1_struct_0(D_113),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_113,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_113))
      | ~ m1_pre_topc(D_113,'#skF_4')
      | ~ m1_pre_topc(D_113,'#skF_1')
      | v2_struct_0(D_113)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_30,c_28,c_26,c_24,c_192,c_189,c_186,c_354])).

tff(c_756,plain,(
    ! [D_239] :
      ( r2_funct_2(u1_struct_0(D_239),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_239,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_239))
      | ~ m1_pre_topc(D_239,'#skF_4')
      | ~ m1_pre_topc(D_239,'#skF_1')
      | v2_struct_0(D_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_32,c_359])).

tff(c_20,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_763,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_756,c_20])).

tff(c_771,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22,c_763])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:14:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.55  
% 3.58/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.55  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.55  
% 3.58/1.55  %Foreground sorts:
% 3.58/1.55  
% 3.58/1.55  
% 3.58/1.55  %Background operators:
% 3.58/1.55  
% 3.58/1.55  
% 3.58/1.55  %Foreground operators:
% 3.58/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.55  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.58/1.55  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.58/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.55  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.58/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.55  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.58/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.55  
% 3.58/1.57  tff(f_220, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 3.58/1.57  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.58/1.57  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.58/1.57  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.58/1.57  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.58/1.57  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.58/1.57  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 3.58/1.57  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_26, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_16, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.58/1.57  tff(c_108, plain, (![C_182, D_179, E_178, A_180, B_181]: (k3_tmap_1(A_180, B_181, C_182, D_179, E_178)=k2_partfun1(u1_struct_0(C_182), u1_struct_0(B_181), E_178, u1_struct_0(D_179)) | ~m1_pre_topc(D_179, C_182) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_182), u1_struct_0(B_181)))) | ~v1_funct_2(E_178, u1_struct_0(C_182), u1_struct_0(B_181)) | ~v1_funct_1(E_178) | ~m1_pre_topc(D_179, A_180) | ~m1_pre_topc(C_182, A_180) | ~l1_pre_topc(B_181) | ~v2_pre_topc(B_181) | v2_struct_0(B_181) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.58/1.57  tff(c_112, plain, (![A_180, D_179]: (k3_tmap_1(A_180, '#skF_2', '#skF_1', D_179, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_179)) | ~m1_pre_topc(D_179, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_179, A_180) | ~m1_pre_topc('#skF_1', A_180) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_24, c_108])).
% 3.58/1.57  tff(c_116, plain, (![A_180, D_179]: (k3_tmap_1(A_180, '#skF_2', '#skF_1', D_179, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_179)) | ~m1_pre_topc(D_179, '#skF_1') | ~m1_pre_topc(D_179, A_180) | ~m1_pre_topc('#skF_1', A_180) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_112])).
% 3.58/1.57  tff(c_118, plain, (![A_183, D_184]: (k3_tmap_1(A_183, '#skF_2', '#skF_1', D_184, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_184)) | ~m1_pre_topc(D_184, '#skF_1') | ~m1_pre_topc(D_184, A_183) | ~m1_pre_topc('#skF_1', A_183) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(negUnitSimplification, [status(thm)], [c_42, c_116])).
% 3.58/1.57  tff(c_122, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_118])).
% 3.58/1.57  tff(c_130, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_30, c_122])).
% 3.58/1.57  tff(c_131, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_130])).
% 3.58/1.57  tff(c_140, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_131])).
% 3.58/1.57  tff(c_144, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_140])).
% 3.58/1.57  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_144])).
% 3.58/1.57  tff(c_150, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_131])).
% 3.58/1.57  tff(c_149, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_131])).
% 3.58/1.57  tff(c_71, plain, (![A_161, B_162, C_163, D_164]: (k2_partfun1(u1_struct_0(A_161), u1_struct_0(B_162), C_163, u1_struct_0(D_164))=k2_tmap_1(A_161, B_162, C_163, D_164) | ~m1_pre_topc(D_164, A_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_161), u1_struct_0(B_162)))) | ~v1_funct_2(C_163, u1_struct_0(A_161), u1_struct_0(B_162)) | ~v1_funct_1(C_163) | ~l1_pre_topc(B_162) | ~v2_pre_topc(B_162) | v2_struct_0(B_162) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.57  tff(c_73, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_164))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_164) | ~m1_pre_topc(D_164, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_71])).
% 3.58/1.57  tff(c_76, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_164))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_164) | ~m1_pre_topc(D_164, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_28, c_26, c_73])).
% 3.58/1.57  tff(c_77, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_164))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_164) | ~m1_pre_topc(D_164, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_76])).
% 3.58/1.57  tff(c_160, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_77])).
% 3.58/1.57  tff(c_167, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_160])).
% 3.58/1.57  tff(c_63, plain, (![B_155, D_157, A_154, C_156, E_158]: (v1_funct_1(k3_tmap_1(A_154, B_155, C_156, D_157, E_158)) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_156), u1_struct_0(B_155)))) | ~v1_funct_2(E_158, u1_struct_0(C_156), u1_struct_0(B_155)) | ~v1_funct_1(E_158) | ~m1_pre_topc(D_157, A_154) | ~m1_pre_topc(C_156, A_154) | ~l1_pre_topc(B_155) | ~v2_pre_topc(B_155) | v2_struct_0(B_155) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.58/1.57  tff(c_65, plain, (![A_154, D_157]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_157, A_154) | ~m1_pre_topc('#skF_1', A_154) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_24, c_63])).
% 3.58/1.57  tff(c_68, plain, (![A_154, D_157]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~m1_pre_topc(D_157, A_154) | ~m1_pre_topc('#skF_1', A_154) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_65])).
% 3.58/1.57  tff(c_69, plain, (![A_154, D_157]: (v1_funct_1(k3_tmap_1(A_154, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~m1_pre_topc(D_157, A_154) | ~m1_pre_topc('#skF_1', A_154) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(negUnitSimplification, [status(thm)], [c_42, c_68])).
% 3.58/1.57  tff(c_181, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_69])).
% 3.58/1.57  tff(c_191, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_150, c_30, c_181])).
% 3.58/1.57  tff(c_192, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_191])).
% 3.58/1.57  tff(c_87, plain, (![D_169, E_170, A_166, B_167, C_168]: (v1_funct_2(k3_tmap_1(A_166, B_167, C_168, D_169, E_170), u1_struct_0(D_169), u1_struct_0(B_167)) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168), u1_struct_0(B_167)))) | ~v1_funct_2(E_170, u1_struct_0(C_168), u1_struct_0(B_167)) | ~v1_funct_1(E_170) | ~m1_pre_topc(D_169, A_166) | ~m1_pre_topc(C_168, A_166) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.58/1.57  tff(c_89, plain, (![A_166, D_169]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_169, A_166) | ~m1_pre_topc('#skF_1', A_166) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_24, c_87])).
% 3.58/1.57  tff(c_92, plain, (![A_166, D_169]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_169, A_166) | ~m1_pre_topc('#skF_1', A_166) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_89])).
% 3.58/1.57  tff(c_93, plain, (![A_166, D_169]: (v1_funct_2(k3_tmap_1(A_166, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_169, A_166) | ~m1_pre_topc('#skF_1', A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(negUnitSimplification, [status(thm)], [c_42, c_92])).
% 3.58/1.57  tff(c_178, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_93])).
% 3.58/1.57  tff(c_188, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_150, c_30, c_178])).
% 3.58/1.57  tff(c_189, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_188])).
% 3.58/1.57  tff(c_10, plain, (![B_52, E_55, C_53, D_54, A_51]: (m1_subset_1(k3_tmap_1(A_51, B_52, C_53, D_54, E_55), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54), u1_struct_0(B_52)))) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.58/1.57  tff(c_175, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_10])).
% 3.58/1.57  tff(c_185, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_150, c_30, c_28, c_26, c_24, c_175])).
% 3.58/1.57  tff(c_186, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_185])).
% 3.58/1.57  tff(c_95, plain, (![E_177, B_174, D_176, C_175, A_173]: (m1_subset_1(k3_tmap_1(A_173, B_174, C_175, D_176, E_177), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_176), u1_struct_0(B_174)))) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_175), u1_struct_0(B_174)))) | ~v1_funct_2(E_177, u1_struct_0(C_175), u1_struct_0(B_174)) | ~v1_funct_1(E_177) | ~m1_pre_topc(D_176, A_173) | ~m1_pre_topc(C_175, A_173) | ~l1_pre_topc(B_174) | ~v2_pre_topc(B_174) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.58/1.57  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.57  tff(c_292, plain, (![B_194, E_193, D_195, A_192, C_191]: (r2_funct_2(u1_struct_0(D_195), u1_struct_0(B_194), k3_tmap_1(A_192, B_194, C_191, D_195, E_193), k3_tmap_1(A_192, B_194, C_191, D_195, E_193)) | ~v1_funct_2(k3_tmap_1(A_192, B_194, C_191, D_195, E_193), u1_struct_0(D_195), u1_struct_0(B_194)) | ~v1_funct_1(k3_tmap_1(A_192, B_194, C_191, D_195, E_193)) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191), u1_struct_0(B_194)))) | ~v1_funct_2(E_193, u1_struct_0(C_191), u1_struct_0(B_194)) | ~v1_funct_1(E_193) | ~m1_pre_topc(D_195, A_192) | ~m1_pre_topc(C_191, A_192) | ~l1_pre_topc(B_194) | ~v2_pre_topc(B_194) | v2_struct_0(B_194) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_95, c_2])).
% 3.58/1.57  tff(c_303, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_292])).
% 3.58/1.57  tff(c_316, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_150, c_30, c_28, c_26, c_24, c_192, c_167, c_189, c_167, c_167, c_303])).
% 3.58/1.57  tff(c_317, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_316])).
% 3.58/1.57  tff(c_18, plain, (![A_57, C_105, B_89, E_117, D_113, F_119]: (r2_funct_2(u1_struct_0(D_113), u1_struct_0(B_89), k3_tmap_1(A_57, B_89, C_105, D_113, F_119), k2_tmap_1(A_57, B_89, E_117, D_113)) | ~m1_pre_topc(D_113, C_105) | ~r2_funct_2(u1_struct_0(C_105), u1_struct_0(B_89), F_119, k2_tmap_1(A_57, B_89, E_117, C_105)) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_105), u1_struct_0(B_89)))) | ~v1_funct_2(F_119, u1_struct_0(C_105), u1_struct_0(B_89)) | ~v1_funct_1(F_119) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57), u1_struct_0(B_89)))) | ~v1_funct_2(E_117, u1_struct_0(A_57), u1_struct_0(B_89)) | ~v1_funct_1(E_117) | ~m1_pre_topc(D_113, A_57) | v2_struct_0(D_113) | ~m1_pre_topc(C_105, A_57) | v2_struct_0(C_105) | ~l1_pre_topc(B_89) | ~v2_pre_topc(B_89) | v2_struct_0(B_89) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.58/1.57  tff(c_354, plain, (![D_113]: (r2_funct_2(u1_struct_0(D_113), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_113, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_113)) | ~m1_pre_topc(D_113, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_113, '#skF_1') | v2_struct_0(D_113) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_317, c_18])).
% 3.58/1.57  tff(c_359, plain, (![D_113]: (r2_funct_2(u1_struct_0(D_113), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_113, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_113)) | ~m1_pre_topc(D_113, '#skF_4') | ~m1_pre_topc(D_113, '#skF_1') | v2_struct_0(D_113) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_30, c_28, c_26, c_24, c_192, c_189, c_186, c_354])).
% 3.58/1.57  tff(c_756, plain, (![D_239]: (r2_funct_2(u1_struct_0(D_239), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_239, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_239)) | ~m1_pre_topc(D_239, '#skF_4') | ~m1_pre_topc(D_239, '#skF_1') | v2_struct_0(D_239))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_32, c_359])).
% 3.58/1.57  tff(c_20, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.58/1.57  tff(c_763, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_756, c_20])).
% 3.58/1.57  tff(c_771, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22, c_763])).
% 3.58/1.57  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_771])).
% 3.58/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.57  
% 3.58/1.57  Inference rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Ref     : 0
% 3.58/1.57  #Sup     : 137
% 3.58/1.57  #Fact    : 0
% 3.58/1.57  #Define  : 0
% 3.58/1.57  #Split   : 4
% 3.58/1.57  #Chain   : 0
% 3.58/1.57  #Close   : 0
% 3.58/1.57  
% 3.58/1.57  Ordering : KBO
% 3.58/1.57  
% 3.58/1.57  Simplification rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Subsume      : 13
% 3.58/1.57  #Demod        : 480
% 3.58/1.57  #Tautology    : 48
% 3.58/1.57  #SimpNegUnit  : 74
% 3.58/1.57  #BackRed      : 3
% 3.58/1.57  
% 3.58/1.57  #Partial instantiations: 0
% 3.58/1.57  #Strategies tried      : 1
% 3.58/1.57  
% 3.58/1.57  Timing (in seconds)
% 3.58/1.57  ----------------------
% 3.58/1.58  Preprocessing        : 0.36
% 3.58/1.58  Parsing              : 0.19
% 3.58/1.58  CNF conversion       : 0.04
% 3.58/1.58  Main loop            : 0.45
% 3.58/1.58  Inferencing          : 0.16
% 3.58/1.58  Reduction            : 0.16
% 3.58/1.58  Demodulation         : 0.12
% 3.58/1.58  BG Simplification    : 0.03
% 3.58/1.58  Subsumption          : 0.09
% 3.58/1.58  Abstraction          : 0.03
% 3.58/1.58  MUC search           : 0.00
% 3.58/1.58  Cooper               : 0.00
% 3.58/1.58  Total                : 0.86
% 3.58/1.58  Index Insertion      : 0.00
% 3.58/1.58  Index Deletion       : 0.00
% 3.58/1.58  Index Matching       : 0.00
% 3.58/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
