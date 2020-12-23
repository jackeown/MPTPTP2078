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
% DateTime   : Thu Dec  3 10:27:44 EST 2020

% Result     : Theorem 10.35s
% Output     : CNFRefutation 10.71s
% Verified   : 
% Statistics : Number of formulae       :  210 (7860 expanded)
%              Number of leaves         :   35 (3033 expanded)
%              Depth                    :   27
%              Number of atoms          :  813 (76894 expanded)
%              Number of equality atoms :   50 (1058 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

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

tff(f_302,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(C,D)
                            & m1_pre_topc(E,C) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( ( v1_funct_1(k3_tmap_1(A,B,D,C,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,C,F),u1_struct_0(C),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,C,F),C,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,C,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                               => ( v1_funct_1(k3_tmap_1(A,B,D,E,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,E,F),u1_struct_0(E),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,E,F),E,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_183,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_241,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_116,axiom,(
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

tff(f_84,axiom,(
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

tff(f_146,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_179,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_229,axiom,(
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
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(D,C)
                          & m1_pre_topc(E,D) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_76,plain,(
    ! [B_195,A_196] :
      ( l1_pre_topc(B_195)
      | ~ m1_pre_topc(B_195,A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_101,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_85])).

tff(c_26,plain,(
    ! [A_66] :
      ( m1_pre_topc(A_66,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_111,plain,(
    ! [B_197,A_198] :
      ( v2_pre_topc(B_197)
      | ~ m1_pre_topc(B_197,A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_136,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_120])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_117,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_133,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_117])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_98,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_82])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_150,plain,(
    ! [C_199,A_200,B_201] :
      ( m1_pre_topc(C_199,A_200)
      | ~ m1_pre_topc(C_199,B_201)
      | ~ m1_pre_topc(B_201,A_200)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_713,plain,(
    ! [A_239] :
      ( m1_pre_topc('#skF_5',A_239)
      | ~ m1_pre_topc('#skF_3',A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_30,plain,(
    ! [C_136,A_130,B_134] :
      ( m1_pre_topc(C_136,A_130)
      | ~ m1_pre_topc(C_136,B_134)
      | ~ m1_pre_topc(B_134,A_130)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_1785,plain,(
    ! [A_341,A_342] :
      ( m1_pre_topc('#skF_5',A_341)
      | ~ m1_pre_topc(A_342,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | ~ m1_pre_topc('#skF_3',A_342)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342) ) ),
    inference(resolution,[status(thm)],[c_713,c_30])).

tff(c_1801,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1785])).

tff(c_1827,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_133,c_98,c_1801])).

tff(c_1847,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1827])).

tff(c_1856,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1847])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1856])).

tff(c_1867,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1827])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_2270,plain,(
    ! [E_402,D_404,A_401,C_403,B_405] :
      ( k3_tmap_1(A_401,B_405,C_403,D_404,E_402) = k2_partfun1(u1_struct_0(C_403),u1_struct_0(B_405),E_402,u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,C_403)
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_403),u1_struct_0(B_405))))
      | ~ v1_funct_2(E_402,u1_struct_0(C_403),u1_struct_0(B_405))
      | ~ v1_funct_1(E_402)
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc(C_403,A_401)
      | ~ l1_pre_topc(B_405)
      | ~ v2_pre_topc(B_405)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2278,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_4',D_404,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(resolution,[status(thm)],[c_42,c_2270])).

tff(c_2290,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_4',D_404,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_4')
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_4',A_401)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_2278])).

tff(c_2292,plain,(
    ! [A_406,D_407] :
      ( k3_tmap_1(A_406,'#skF_2','#skF_4',D_407,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_407))
      | ~ m1_pre_topc(D_407,'#skF_4')
      | ~ m1_pre_topc(D_407,A_406)
      | ~ m1_pre_topc('#skF_4',A_406)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2290])).

tff(c_2316,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2292])).

tff(c_2357,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_1867,c_2316])).

tff(c_2358,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2357])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_2140,plain,(
    ! [A_368,B_369,C_370,D_371] :
      ( k2_partfun1(u1_struct_0(A_368),u1_struct_0(B_369),C_370,u1_struct_0(D_371)) = k2_tmap_1(A_368,B_369,C_370,D_371)
      | ~ m1_pre_topc(D_371,A_368)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368),u1_struct_0(B_369))))
      | ~ v1_funct_2(C_370,u1_struct_0(A_368),u1_struct_0(B_369))
      | ~ v1_funct_1(C_370)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2146,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_371)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_371)
      | ~ m1_pre_topc(D_371,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_2140])).

tff(c_2157,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_371)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_371)
      | ~ m1_pre_topc(D_371,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_98,c_66,c_64,c_46,c_44,c_2146])).

tff(c_2158,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_371)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_371)
      | ~ m1_pre_topc(D_371,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_2157])).

tff(c_2497,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_2158])).

tff(c_2504,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_2497])).

tff(c_1755,plain,(
    ! [C_338,B_334,A_336,E_335,D_337] :
      ( v1_funct_2(k3_tmap_1(A_336,B_334,C_338,D_337,E_335),u1_struct_0(D_337),u1_struct_0(B_334))
      | ~ m1_subset_1(E_335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338),u1_struct_0(B_334))))
      | ~ v1_funct_2(E_335,u1_struct_0(C_338),u1_struct_0(B_334))
      | ~ v1_funct_1(E_335)
      | ~ m1_pre_topc(D_337,A_336)
      | ~ m1_pre_topc(C_338,A_336)
      | ~ l1_pre_topc(B_334)
      | ~ v2_pre_topc(B_334)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1761,plain,(
    ! [A_336,D_337] :
      ( v1_funct_2(k3_tmap_1(A_336,'#skF_2','#skF_4',D_337,'#skF_6'),u1_struct_0(D_337),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_337,A_336)
      | ~ m1_pre_topc('#skF_4',A_336)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_42,c_1755])).

tff(c_1772,plain,(
    ! [A_336,D_337] :
      ( v1_funct_2(k3_tmap_1(A_336,'#skF_2','#skF_4',D_337,'#skF_6'),u1_struct_0(D_337),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_337,A_336)
      | ~ m1_pre_topc('#skF_4',A_336)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_1761])).

tff(c_1774,plain,(
    ! [A_339,D_340] :
      ( v1_funct_2(k3_tmap_1(A_339,'#skF_2','#skF_4',D_340,'#skF_6'),u1_struct_0(D_340),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_340,A_339)
      | ~ m1_pre_topc('#skF_4',A_339)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1772])).

tff(c_1235,plain,(
    ! [A_296,B_294,D_297,E_295,C_298] :
      ( m1_subset_1(k3_tmap_1(A_296,B_294,C_298,D_297,E_295),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_297),u1_struct_0(B_294))))
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298),u1_struct_0(B_294))))
      | ~ v1_funct_2(E_295,u1_struct_0(C_298),u1_struct_0(B_294))
      | ~ v1_funct_1(E_295)
      | ~ m1_pre_topc(D_297,A_296)
      | ~ m1_pre_topc(C_298,A_296)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_661,plain,(
    ! [C_234,A_232,D_233,E_231,B_230] :
      ( v1_funct_1(k3_tmap_1(A_232,B_230,C_234,D_233,E_231))
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_234),u1_struct_0(B_230))))
      | ~ v1_funct_2(E_231,u1_struct_0(C_234),u1_struct_0(B_230))
      | ~ v1_funct_1(E_231)
      | ~ m1_pre_topc(D_233,A_232)
      | ~ m1_pre_topc(C_234,A_232)
      | ~ l1_pre_topc(B_230)
      | ~ v2_pre_topc(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_665,plain,(
    ! [A_232,D_233] :
      ( v1_funct_1(k3_tmap_1(A_232,'#skF_2','#skF_4',D_233,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_233,A_232)
      | ~ m1_pre_topc('#skF_4',A_232)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_42,c_661])).

tff(c_672,plain,(
    ! [A_232,D_233] :
      ( v1_funct_1(k3_tmap_1(A_232,'#skF_2','#skF_4',D_233,'#skF_6'))
      | ~ m1_pre_topc(D_233,A_232)
      | ~ m1_pre_topc('#skF_4',A_232)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_665])).

tff(c_674,plain,(
    ! [A_235,D_236] :
      ( v1_funct_1(k3_tmap_1(A_235,'#skF_2','#skF_4',D_236,'#skF_6'))
      | ~ m1_pre_topc(D_236,A_235)
      | ~ m1_pre_topc('#skF_4',A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_672])).

tff(c_32,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_202,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_677,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_674,c_202])).

tff(c_680,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_52,c_677])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_680])).

tff(c_683,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_727,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_1250,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1235,c_727])).

tff(c_1261,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_56,c_52,c_46,c_44,c_42,c_1250])).

tff(c_1263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1261])).

tff(c_1264,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_1371,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1264])).

tff(c_1777,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1774,c_1371])).

tff(c_1780,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_52,c_1777])).

tff(c_1782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1780])).

tff(c_1783,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_2514,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_1783])).

tff(c_2312,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2292])).

tff(c_2349,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_50,c_2312])).

tff(c_2350,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2349])).

tff(c_2366,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2350,c_2158])).

tff(c_2373,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2366])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_40,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_38,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_36,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_34,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_2247,plain,(
    ! [A_396,B_397,C_398,D_399] :
      ( v1_funct_2(k2_tmap_1(A_396,B_397,C_398,D_399),u1_struct_0(D_399),u1_struct_0(B_397))
      | ~ m1_pre_topc(D_399,A_396)
      | v2_struct_0(D_399)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396),u1_struct_0(B_397))))
      | ~ v5_pre_topc(C_398,A_396,B_397)
      | ~ v1_funct_2(C_398,u1_struct_0(A_396),u1_struct_0(B_397))
      | ~ v1_funct_1(C_398)
      | ~ l1_pre_topc(B_397)
      | ~ v2_pre_topc(B_397)
      | v2_struct_0(B_397)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2253,plain,(
    ! [D_399] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_399),u1_struct_0(D_399),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_399,'#skF_3')
      | v2_struct_0(D_399)
      | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2247])).

tff(c_2263,plain,(
    ! [D_399] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_399),u1_struct_0(D_399),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_399,'#skF_3')
      | v2_struct_0(D_399)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_66,c_64,c_40,c_38,c_36,c_2253])).

tff(c_2264,plain,(
    ! [D_399] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_399),u1_struct_0(D_399),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_399,'#skF_3')
      | v2_struct_0(D_399) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_2263])).

tff(c_2378,plain,(
    ! [D_399] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_399),u1_struct_0(D_399),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_399,'#skF_3')
      | v2_struct_0(D_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2264])).

tff(c_2119,plain,(
    ! [A_363,B_364,C_365,D_366] :
      ( v1_funct_1(k2_tmap_1(A_363,B_364,C_365,D_366))
      | ~ m1_pre_topc(D_366,A_363)
      | v2_struct_0(D_366)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0(B_364))))
      | ~ v5_pre_topc(C_365,A_363,B_364)
      | ~ v1_funct_2(C_365,u1_struct_0(A_363),u1_struct_0(B_364))
      | ~ v1_funct_1(C_365)
      | ~ l1_pre_topc(B_364)
      | ~ v2_pre_topc(B_364)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2123,plain,(
    ! [D_366] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_366))
      | ~ m1_pre_topc(D_366,'#skF_3')
      | v2_struct_0(D_366)
      | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2119])).

tff(c_2132,plain,(
    ! [D_366] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_366))
      | ~ m1_pre_topc(D_366,'#skF_3')
      | v2_struct_0(D_366)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_66,c_64,c_40,c_38,c_36,c_2123])).

tff(c_2133,plain,(
    ! [D_366] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_366))
      | ~ m1_pre_topc(D_366,'#skF_3')
      | v2_struct_0(D_366) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_2132])).

tff(c_2382,plain,(
    ! [D_366] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_366))
      | ~ m1_pre_topc(D_366,'#skF_3')
      | v2_struct_0(D_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2133])).

tff(c_2144,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_371)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_371)
      | ~ m1_pre_topc(D_371,'#skF_3')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2140])).

tff(c_2153,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_371)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_371)
      | ~ m1_pre_topc(D_371,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_66,c_64,c_40,c_38,c_2144])).

tff(c_2154,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_371)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_371)
      | ~ m1_pre_topc(D_371,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_2153])).

tff(c_2381,plain,(
    ! [D_371] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_371)) = k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_371)
      | ~ m1_pre_topc(D_371,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2373,c_2154])).

tff(c_1868,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1827])).

tff(c_2388,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_40])).

tff(c_2386,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_38])).

tff(c_2385,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_34])).

tff(c_2276,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_3',D_404,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_3')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(resolution,[status(thm)],[c_34,c_2270])).

tff(c_2286,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_3',D_404,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_3')
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_38,c_2276])).

tff(c_2287,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_3',D_404,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_3')
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2286])).

tff(c_2660,plain,(
    ! [A_417,D_418] :
      ( k3_tmap_1(A_417,'#skF_2','#skF_3',D_418,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_418))
      | ~ m1_pre_topc(D_418,'#skF_3')
      | ~ m1_pre_topc(D_418,A_417)
      | ~ m1_pre_topc('#skF_3',A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2373,c_2287])).

tff(c_14,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( m1_subset_1(k3_tmap_1(A_57,B_58,C_59,D_60,E_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60),u1_struct_0(B_58))))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2675,plain,(
    ! [D_418,A_417] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_418)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_418),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'))
      | ~ m1_pre_topc(D_418,A_417)
      | ~ m1_pre_topc('#skF_3',A_417)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417)
      | ~ m1_pre_topc(D_418,'#skF_3')
      | ~ m1_pre_topc(D_418,A_417)
      | ~ m1_pre_topc('#skF_3',A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2660,c_14])).

tff(c_2690,plain,(
    ! [D_418,A_417] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_418)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_418),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_418,'#skF_3')
      | ~ m1_pre_topc(D_418,A_417)
      | ~ m1_pre_topc('#skF_3',A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2388,c_2386,c_2385,c_2675])).

tff(c_4600,plain,(
    ! [D_524,A_525] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_524)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_524),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_524,'#skF_3')
      | ~ m1_pre_topc(D_524,A_525)
      | ~ m1_pre_topc('#skF_3',A_525)
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2690])).

tff(c_4630,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_4600])).

tff(c_4681,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_1868,c_48,c_4630])).

tff(c_4682,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4681])).

tff(c_4831,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_4682])).

tff(c_4873,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4831])).

tff(c_684,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2516,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_684])).

tff(c_1784,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_2513,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_1784])).

tff(c_2526,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_14])).

tff(c_2542,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_56,c_52,c_46,c_44,c_42,c_2526])).

tff(c_2543,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2542])).

tff(c_3342,plain,(
    ! [D_460] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_460)) = k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_460)
      | ~ m1_pre_topc(D_460,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2373,c_2154])).

tff(c_2659,plain,(
    ! [A_401,D_404] :
      ( k3_tmap_1(A_401,'#skF_2','#skF_3',D_404,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_3')
      | ~ m1_pre_topc(D_404,A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2373,c_2287])).

tff(c_6582,plain,(
    ! [A_572,D_573] :
      ( k3_tmap_1(A_572,'#skF_2','#skF_3',D_573,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_573)
      | ~ m1_pre_topc(D_573,'#skF_3')
      | ~ m1_pre_topc(D_573,A_572)
      | ~ m1_pre_topc('#skF_3',A_572)
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572)
      | v2_struct_0(A_572)
      | ~ m1_pre_topc(D_573,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3342,c_2659])).

tff(c_2310,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_2292])).

tff(c_2345,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_2310])).

tff(c_2346,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2345])).

tff(c_2700,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2346])).

tff(c_2703,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2700])).

tff(c_2707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2703])).

tff(c_2709,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2346])).

tff(c_2508,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_2358])).

tff(c_2298,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1867,c_2292])).

tff(c_2328,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_98,c_1867,c_2298])).

tff(c_2329,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2328])).

tff(c_3100,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_5','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_2508,c_2329])).

tff(c_2377,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2350])).

tff(c_2314,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2292])).

tff(c_2353,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_98,c_50,c_2314])).

tff(c_2354,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2353])).

tff(c_3044,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_2377,c_2354])).

tff(c_28,plain,(
    ! [E_127,C_115,F_129,D_123,B_99,A_67] :
      ( r2_funct_2(u1_struct_0(E_127),u1_struct_0(B_99),k3_tmap_1(A_67,B_99,D_123,E_127,k3_tmap_1(A_67,B_99,C_115,D_123,F_129)),k3_tmap_1(A_67,B_99,C_115,E_127,F_129))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_115),u1_struct_0(B_99))))
      | ~ v1_funct_2(F_129,u1_struct_0(C_115),u1_struct_0(B_99))
      | ~ v1_funct_1(F_129)
      | ~ m1_pre_topc(E_127,D_123)
      | ~ m1_pre_topc(D_123,C_115)
      | ~ m1_pre_topc(E_127,A_67)
      | v2_struct_0(E_127)
      | ~ m1_pre_topc(D_123,A_67)
      | v2_struct_0(D_123)
      | ~ m1_pre_topc(C_115,A_67)
      | v2_struct_0(C_115)
      | ~ l1_pre_topc(B_99)
      | ~ v2_pre_topc(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_3056,plain,(
    ! [E_127] :
      ( r2_funct_2(u1_struct_0(E_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3',E_127,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k3_tmap_1('#skF_4','#skF_2','#skF_4',E_127,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(E_127,'#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc(E_127,'#skF_4')
      | v2_struct_0(E_127)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3044,c_28])).

tff(c_3081,plain,(
    ! [E_127] :
      ( r2_funct_2(u1_struct_0(E_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3',E_127,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k3_tmap_1('#skF_4','#skF_2','#skF_4',E_127,'#skF_6'))
      | ~ m1_pre_topc(E_127,'#skF_3')
      | ~ m1_pre_topc(E_127,'#skF_4')
      | v2_struct_0(E_127)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_98,c_66,c_64,c_2709,c_50,c_50,c_46,c_44,c_42,c_3056])).

tff(c_4010,plain,(
    ! [E_504] :
      ( r2_funct_2(u1_struct_0(E_504),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3',E_504,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k3_tmap_1('#skF_4','#skF_2','#skF_4',E_504,'#skF_6'))
      | ~ m1_pre_topc(E_504,'#skF_3')
      | ~ m1_pre_topc(E_504,'#skF_4')
      | v2_struct_0(E_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_62,c_3081])).

tff(c_4015,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3100,c_4010])).

tff(c_4024,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_48,c_4015])).

tff(c_4025,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4024])).

tff(c_6602,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6582,c_4025])).

tff(c_6680,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_133,c_98,c_50,c_1867,c_48,c_6602])).

tff(c_6681,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6680])).

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

tff(c_6732,plain,
    ( k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_6681,c_4])).

tff(c_6735,plain,
    ( k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4873,c_2516,c_2513,c_2543,c_6732])).

tff(c_8410,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6735])).

tff(c_8413,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2382,c_8410])).

tff(c_8416,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8413])).

tff(c_8418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8416])).

tff(c_8419,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6735])).

tff(c_8428,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8419])).

tff(c_8431,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2378,c_8428])).

tff(c_8434,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8431])).

tff(c_8436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8434])).

tff(c_8437,plain,(
    k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8419])).

tff(c_2208,plain,(
    ! [A_386,B_387,C_388,D_389] :
      ( v5_pre_topc(k2_tmap_1(A_386,B_387,C_388,D_389),D_389,B_387)
      | ~ m1_pre_topc(D_389,A_386)
      | v2_struct_0(D_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_386),u1_struct_0(B_387))))
      | ~ v5_pre_topc(C_388,A_386,B_387)
      | ~ v1_funct_2(C_388,u1_struct_0(A_386),u1_struct_0(B_387))
      | ~ v1_funct_1(C_388)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2212,plain,(
    ! [D_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_389),D_389,'#skF_2')
      | ~ m1_pre_topc(D_389,'#skF_3')
      | v2_struct_0(D_389)
      | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2208])).

tff(c_2221,plain,(
    ! [D_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_389),D_389,'#skF_2')
      | ~ m1_pre_topc(D_389,'#skF_3')
      | v2_struct_0(D_389)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_66,c_64,c_40,c_38,c_36,c_2212])).

tff(c_2222,plain,(
    ! [D_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_389),D_389,'#skF_2')
      | ~ m1_pre_topc(D_389,'#skF_3')
      | v2_struct_0(D_389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_2221])).

tff(c_2379,plain,(
    ! [D_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_389),D_389,'#skF_2')
      | ~ m1_pre_topc(D_389,'#skF_3')
      | v2_struct_0(D_389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2222])).

tff(c_8460,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8437,c_2379])).

tff(c_8479,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8460])).

tff(c_8481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2514,c_8479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:26:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.35/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/3.68  
% 10.52/3.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/3.69  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.52/3.69  
% 10.52/3.69  %Foreground sorts:
% 10.52/3.69  
% 10.52/3.69  
% 10.52/3.69  %Background operators:
% 10.52/3.69  
% 10.52/3.69  
% 10.52/3.69  %Foreground operators:
% 10.52/3.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.52/3.69  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 10.52/3.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.52/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.52/3.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.52/3.69  tff('#skF_5', type, '#skF_5': $i).
% 10.52/3.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.52/3.69  tff('#skF_6', type, '#skF_6': $i).
% 10.52/3.69  tff('#skF_2', type, '#skF_2': $i).
% 10.52/3.69  tff('#skF_3', type, '#skF_3': $i).
% 10.52/3.69  tff('#skF_1', type, '#skF_1': $i).
% 10.52/3.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.52/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.52/3.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.52/3.69  tff('#skF_4', type, '#skF_4': $i).
% 10.52/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.52/3.69  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 10.52/3.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.52/3.69  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.52/3.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.52/3.69  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.52/3.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.52/3.69  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.52/3.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.52/3.69  
% 10.71/3.72  tff(f_302, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(C, D) & m1_pre_topc(E, C)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((v1_funct_1(k3_tmap_1(A, B, D, C, F)) & v1_funct_2(k3_tmap_1(A, B, D, C, F), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, C, F), C, B)) & m1_subset_1(k3_tmap_1(A, B, D, C, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (((v1_funct_1(k3_tmap_1(A, B, D, E, F)) & v1_funct_2(k3_tmap_1(A, B, D, E, F), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, E, F), E, B)) & m1_subset_1(k3_tmap_1(A, B, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_tmap_1)).
% 10.71/3.72  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.71/3.72  tff(f_183, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 10.71/3.72  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 10.71/3.72  tff(f_241, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 10.71/3.72  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 10.71/3.72  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 10.71/3.72  tff(f_146, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 10.71/3.72  tff(f_179, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tmap_1)).
% 10.71/3.72  tff(f_229, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 10.71/3.72  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 10.71/3.72  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_76, plain, (![B_195, A_196]: (l1_pre_topc(B_195) | ~m1_pre_topc(B_195, A_196) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.71/3.72  tff(c_85, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_76])).
% 10.71/3.72  tff(c_101, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_85])).
% 10.71/3.72  tff(c_26, plain, (![A_66]: (m1_pre_topc(A_66, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.71/3.72  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_111, plain, (![B_197, A_198]: (v2_pre_topc(B_197) | ~m1_pre_topc(B_197, A_198) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.71/3.72  tff(c_120, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_111])).
% 10.71/3.72  tff(c_136, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_120])).
% 10.71/3.72  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_117, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_111])).
% 10.71/3.72  tff(c_133, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_117])).
% 10.71/3.72  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_76])).
% 10.71/3.72  tff(c_98, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_82])).
% 10.71/3.72  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_150, plain, (![C_199, A_200, B_201]: (m1_pre_topc(C_199, A_200) | ~m1_pre_topc(C_199, B_201) | ~m1_pre_topc(B_201, A_200) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_241])).
% 10.71/3.72  tff(c_713, plain, (![A_239]: (m1_pre_topc('#skF_5', A_239) | ~m1_pre_topc('#skF_3', A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(resolution, [status(thm)], [c_48, c_150])).
% 10.71/3.72  tff(c_30, plain, (![C_136, A_130, B_134]: (m1_pre_topc(C_136, A_130) | ~m1_pre_topc(C_136, B_134) | ~m1_pre_topc(B_134, A_130) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_241])).
% 10.71/3.72  tff(c_1785, plain, (![A_341, A_342]: (m1_pre_topc('#skF_5', A_341) | ~m1_pre_topc(A_342, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | ~m1_pre_topc('#skF_3', A_342) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342))), inference(resolution, [status(thm)], [c_713, c_30])).
% 10.71/3.72  tff(c_1801, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1785])).
% 10.71/3.72  tff(c_1827, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_133, c_98, c_1801])).
% 10.71/3.72  tff(c_1847, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1827])).
% 10.71/3.72  tff(c_1856, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1847])).
% 10.71/3.72  tff(c_1866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_1856])).
% 10.71/3.72  tff(c_1867, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1827])).
% 10.71/3.72  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_2270, plain, (![E_402, D_404, A_401, C_403, B_405]: (k3_tmap_1(A_401, B_405, C_403, D_404, E_402)=k2_partfun1(u1_struct_0(C_403), u1_struct_0(B_405), E_402, u1_struct_0(D_404)) | ~m1_pre_topc(D_404, C_403) | ~m1_subset_1(E_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_403), u1_struct_0(B_405)))) | ~v1_funct_2(E_402, u1_struct_0(C_403), u1_struct_0(B_405)) | ~v1_funct_1(E_402) | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc(C_403, A_401) | ~l1_pre_topc(B_405) | ~v2_pre_topc(B_405) | v2_struct_0(B_405) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.71/3.72  tff(c_2278, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_4', D_404, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_4', A_401) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(resolution, [status(thm)], [c_42, c_2270])).
% 10.71/3.72  tff(c_2290, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_4', D_404, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_4') | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_4', A_401) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_2278])).
% 10.71/3.72  tff(c_2292, plain, (![A_406, D_407]: (k3_tmap_1(A_406, '#skF_2', '#skF_4', D_407, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_407)) | ~m1_pre_topc(D_407, '#skF_4') | ~m1_pre_topc(D_407, A_406) | ~m1_pre_topc('#skF_4', A_406) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(negUnitSimplification, [status(thm)], [c_68, c_2290])).
% 10.71/3.72  tff(c_2316, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2292])).
% 10.71/3.72  tff(c_2357, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_1867, c_2316])).
% 10.71/3.72  tff(c_2358, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_2357])).
% 10.71/3.72  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_2140, plain, (![A_368, B_369, C_370, D_371]: (k2_partfun1(u1_struct_0(A_368), u1_struct_0(B_369), C_370, u1_struct_0(D_371))=k2_tmap_1(A_368, B_369, C_370, D_371) | ~m1_pre_topc(D_371, A_368) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368), u1_struct_0(B_369)))) | ~v1_funct_2(C_370, u1_struct_0(A_368), u1_struct_0(B_369)) | ~v1_funct_1(C_370) | ~l1_pre_topc(B_369) | ~v2_pre_topc(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.71/3.72  tff(c_2146, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_371))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_371) | ~m1_pre_topc(D_371, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_2140])).
% 10.71/3.72  tff(c_2157, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_371))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_371) | ~m1_pre_topc(D_371, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_98, c_66, c_64, c_46, c_44, c_2146])).
% 10.71/3.72  tff(c_2158, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_371))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_371) | ~m1_pre_topc(D_371, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_2157])).
% 10.71/3.72  tff(c_2497, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2358, c_2158])).
% 10.71/3.72  tff(c_2504, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_2497])).
% 10.71/3.72  tff(c_1755, plain, (![C_338, B_334, A_336, E_335, D_337]: (v1_funct_2(k3_tmap_1(A_336, B_334, C_338, D_337, E_335), u1_struct_0(D_337), u1_struct_0(B_334)) | ~m1_subset_1(E_335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338), u1_struct_0(B_334)))) | ~v1_funct_2(E_335, u1_struct_0(C_338), u1_struct_0(B_334)) | ~v1_funct_1(E_335) | ~m1_pre_topc(D_337, A_336) | ~m1_pre_topc(C_338, A_336) | ~l1_pre_topc(B_334) | ~v2_pre_topc(B_334) | v2_struct_0(B_334) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.71/3.72  tff(c_1761, plain, (![A_336, D_337]: (v1_funct_2(k3_tmap_1(A_336, '#skF_2', '#skF_4', D_337, '#skF_6'), u1_struct_0(D_337), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_337, A_336) | ~m1_pre_topc('#skF_4', A_336) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_42, c_1755])).
% 10.71/3.72  tff(c_1772, plain, (![A_336, D_337]: (v1_funct_2(k3_tmap_1(A_336, '#skF_2', '#skF_4', D_337, '#skF_6'), u1_struct_0(D_337), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_337, A_336) | ~m1_pre_topc('#skF_4', A_336) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_1761])).
% 10.71/3.72  tff(c_1774, plain, (![A_339, D_340]: (v1_funct_2(k3_tmap_1(A_339, '#skF_2', '#skF_4', D_340, '#skF_6'), u1_struct_0(D_340), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_340, A_339) | ~m1_pre_topc('#skF_4', A_339) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(negUnitSimplification, [status(thm)], [c_68, c_1772])).
% 10.71/3.72  tff(c_1235, plain, (![A_296, B_294, D_297, E_295, C_298]: (m1_subset_1(k3_tmap_1(A_296, B_294, C_298, D_297, E_295), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_297), u1_struct_0(B_294)))) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298), u1_struct_0(B_294)))) | ~v1_funct_2(E_295, u1_struct_0(C_298), u1_struct_0(B_294)) | ~v1_funct_1(E_295) | ~m1_pre_topc(D_297, A_296) | ~m1_pre_topc(C_298, A_296) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.71/3.72  tff(c_661, plain, (![C_234, A_232, D_233, E_231, B_230]: (v1_funct_1(k3_tmap_1(A_232, B_230, C_234, D_233, E_231)) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_234), u1_struct_0(B_230)))) | ~v1_funct_2(E_231, u1_struct_0(C_234), u1_struct_0(B_230)) | ~v1_funct_1(E_231) | ~m1_pre_topc(D_233, A_232) | ~m1_pre_topc(C_234, A_232) | ~l1_pre_topc(B_230) | ~v2_pre_topc(B_230) | v2_struct_0(B_230) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.71/3.72  tff(c_665, plain, (![A_232, D_233]: (v1_funct_1(k3_tmap_1(A_232, '#skF_2', '#skF_4', D_233, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_233, A_232) | ~m1_pre_topc('#skF_4', A_232) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_42, c_661])).
% 10.71/3.72  tff(c_672, plain, (![A_232, D_233]: (v1_funct_1(k3_tmap_1(A_232, '#skF_2', '#skF_4', D_233, '#skF_6')) | ~m1_pre_topc(D_233, A_232) | ~m1_pre_topc('#skF_4', A_232) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_665])).
% 10.71/3.72  tff(c_674, plain, (![A_235, D_236]: (v1_funct_1(k3_tmap_1(A_235, '#skF_2', '#skF_4', D_236, '#skF_6')) | ~m1_pre_topc(D_236, A_235) | ~m1_pre_topc('#skF_4', A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(negUnitSimplification, [status(thm)], [c_68, c_672])).
% 10.71/3.72  tff(c_32, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_202, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_32])).
% 10.71/3.72  tff(c_677, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_674, c_202])).
% 10.71/3.72  tff(c_680, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_52, c_677])).
% 10.71/3.72  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_680])).
% 10.71/3.72  tff(c_683, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_32])).
% 10.71/3.72  tff(c_727, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_683])).
% 10.71/3.72  tff(c_1250, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1235, c_727])).
% 10.71/3.72  tff(c_1261, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_56, c_52, c_46, c_44, c_42, c_1250])).
% 10.71/3.72  tff(c_1263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1261])).
% 10.71/3.72  tff(c_1264, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_683])).
% 10.71/3.72  tff(c_1371, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1264])).
% 10.71/3.72  tff(c_1777, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1774, c_1371])).
% 10.71/3.72  tff(c_1780, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_52, c_1777])).
% 10.71/3.72  tff(c_1782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1780])).
% 10.71/3.72  tff(c_1783, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_1264])).
% 10.71/3.72  tff(c_2514, plain, (~v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_1783])).
% 10.71/3.72  tff(c_2312, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2292])).
% 10.71/3.72  tff(c_2349, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_50, c_2312])).
% 10.71/3.72  tff(c_2350, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_2349])).
% 10.71/3.72  tff(c_2366, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2350, c_2158])).
% 10.71/3.72  tff(c_2373, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2366])).
% 10.71/3.72  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_40, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_38, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_36, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_34, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 10.71/3.72  tff(c_2247, plain, (![A_396, B_397, C_398, D_399]: (v1_funct_2(k2_tmap_1(A_396, B_397, C_398, D_399), u1_struct_0(D_399), u1_struct_0(B_397)) | ~m1_pre_topc(D_399, A_396) | v2_struct_0(D_399) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396), u1_struct_0(B_397)))) | ~v5_pre_topc(C_398, A_396, B_397) | ~v1_funct_2(C_398, u1_struct_0(A_396), u1_struct_0(B_397)) | ~v1_funct_1(C_398) | ~l1_pre_topc(B_397) | ~v2_pre_topc(B_397) | v2_struct_0(B_397) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.71/3.72  tff(c_2253, plain, (![D_399]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_399), u1_struct_0(D_399), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_399, '#skF_3') | v2_struct_0(D_399) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2247])).
% 10.71/3.72  tff(c_2263, plain, (![D_399]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_399), u1_struct_0(D_399), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_399, '#skF_3') | v2_struct_0(D_399) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_66, c_64, c_40, c_38, c_36, c_2253])).
% 10.71/3.72  tff(c_2264, plain, (![D_399]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_399), u1_struct_0(D_399), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_399, '#skF_3') | v2_struct_0(D_399))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_2263])).
% 10.71/3.72  tff(c_2378, plain, (![D_399]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_399), u1_struct_0(D_399), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_399, '#skF_3') | v2_struct_0(D_399))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2264])).
% 10.71/3.72  tff(c_2119, plain, (![A_363, B_364, C_365, D_366]: (v1_funct_1(k2_tmap_1(A_363, B_364, C_365, D_366)) | ~m1_pre_topc(D_366, A_363) | v2_struct_0(D_366) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0(B_364)))) | ~v5_pre_topc(C_365, A_363, B_364) | ~v1_funct_2(C_365, u1_struct_0(A_363), u1_struct_0(B_364)) | ~v1_funct_1(C_365) | ~l1_pre_topc(B_364) | ~v2_pre_topc(B_364) | v2_struct_0(B_364) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.71/3.72  tff(c_2123, plain, (![D_366]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_366)) | ~m1_pre_topc(D_366, '#skF_3') | v2_struct_0(D_366) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2119])).
% 10.71/3.72  tff(c_2132, plain, (![D_366]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_366)) | ~m1_pre_topc(D_366, '#skF_3') | v2_struct_0(D_366) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_66, c_64, c_40, c_38, c_36, c_2123])).
% 10.71/3.72  tff(c_2133, plain, (![D_366]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_366)) | ~m1_pre_topc(D_366, '#skF_3') | v2_struct_0(D_366))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_2132])).
% 10.71/3.72  tff(c_2382, plain, (![D_366]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_366)) | ~m1_pre_topc(D_366, '#skF_3') | v2_struct_0(D_366))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2133])).
% 10.71/3.72  tff(c_2144, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_371))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_371) | ~m1_pre_topc(D_371, '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2140])).
% 10.71/3.72  tff(c_2153, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_371))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_371) | ~m1_pre_topc(D_371, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_66, c_64, c_40, c_38, c_2144])).
% 10.71/3.72  tff(c_2154, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_371))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_371) | ~m1_pre_topc(D_371, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_2153])).
% 10.71/3.72  tff(c_2381, plain, (![D_371]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_371))=k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_371) | ~m1_pre_topc(D_371, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2373, c_2154])).
% 10.71/3.72  tff(c_1868, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1827])).
% 10.71/3.72  tff(c_2388, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_40])).
% 10.71/3.72  tff(c_2386, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_38])).
% 10.71/3.72  tff(c_2385, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_34])).
% 10.71/3.72  tff(c_2276, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_3', D_404, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_3', A_401) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(resolution, [status(thm)], [c_34, c_2270])).
% 10.71/3.72  tff(c_2286, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_3', D_404, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_3') | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_3', A_401) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_38, c_2276])).
% 10.71/3.72  tff(c_2287, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_3', D_404, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_3') | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_3', A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(negUnitSimplification, [status(thm)], [c_68, c_2286])).
% 10.71/3.72  tff(c_2660, plain, (![A_417, D_418]: (k3_tmap_1(A_417, '#skF_2', '#skF_3', D_418, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_418)) | ~m1_pre_topc(D_418, '#skF_3') | ~m1_pre_topc(D_418, A_417) | ~m1_pre_topc('#skF_3', A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2373, c_2287])).
% 10.71/3.72  tff(c_14, plain, (![A_57, E_61, B_58, D_60, C_59]: (m1_subset_1(k3_tmap_1(A_57, B_58, C_59, D_60, E_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60), u1_struct_0(B_58)))) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.71/3.72  tff(c_2675, plain, (![D_418, A_417]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_418)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_418), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')) | ~m1_pre_topc(D_418, A_417) | ~m1_pre_topc('#skF_3', A_417) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417) | ~m1_pre_topc(D_418, '#skF_3') | ~m1_pre_topc(D_418, A_417) | ~m1_pre_topc('#skF_3', A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(superposition, [status(thm), theory('equality')], [c_2660, c_14])).
% 10.71/3.72  tff(c_2690, plain, (![D_418, A_417]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_418)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_418), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_418, '#skF_3') | ~m1_pre_topc(D_418, A_417) | ~m1_pre_topc('#skF_3', A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2388, c_2386, c_2385, c_2675])).
% 10.71/3.72  tff(c_4600, plain, (![D_524, A_525]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_524)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_524), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_524, '#skF_3') | ~m1_pre_topc(D_524, A_525) | ~m1_pre_topc('#skF_3', A_525) | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(negUnitSimplification, [status(thm)], [c_68, c_2690])).
% 10.71/3.72  tff(c_4630, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_4600])).
% 10.71/3.72  tff(c_4681, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_1868, c_48, c_4630])).
% 10.71/3.72  tff(c_4682, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_4681])).
% 10.71/3.72  tff(c_4831, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2381, c_4682])).
% 10.71/3.72  tff(c_4873, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4831])).
% 10.71/3.72  tff(c_684, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_32])).
% 10.71/3.72  tff(c_2516, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_684])).
% 10.71/3.72  tff(c_1784, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1264])).
% 10.71/3.72  tff(c_2513, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_1784])).
% 10.71/3.72  tff(c_2526, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2504, c_14])).
% 10.71/3.72  tff(c_2542, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_56, c_52, c_46, c_44, c_42, c_2526])).
% 10.71/3.72  tff(c_2543, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2542])).
% 10.71/3.72  tff(c_3342, plain, (![D_460]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_460))=k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_460) | ~m1_pre_topc(D_460, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2373, c_2154])).
% 10.71/3.72  tff(c_2659, plain, (![A_401, D_404]: (k3_tmap_1(A_401, '#skF_2', '#skF_3', D_404, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_3') | ~m1_pre_topc(D_404, A_401) | ~m1_pre_topc('#skF_3', A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2373, c_2287])).
% 10.71/3.72  tff(c_6582, plain, (![A_572, D_573]: (k3_tmap_1(A_572, '#skF_2', '#skF_3', D_573, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_573) | ~m1_pre_topc(D_573, '#skF_3') | ~m1_pre_topc(D_573, A_572) | ~m1_pre_topc('#skF_3', A_572) | ~l1_pre_topc(A_572) | ~v2_pre_topc(A_572) | v2_struct_0(A_572) | ~m1_pre_topc(D_573, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3342, c_2659])).
% 10.71/3.72  tff(c_2310, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_2292])).
% 10.71/3.72  tff(c_2345, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_2310])).
% 10.71/3.72  tff(c_2346, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_2345])).
% 10.71/3.72  tff(c_2700, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_2346])).
% 10.71/3.72  tff(c_2703, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2700])).
% 10.71/3.72  tff(c_2707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_2703])).
% 10.71/3.72  tff(c_2709, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_2346])).
% 10.71/3.72  tff(c_2508, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_2358])).
% 10.71/3.72  tff(c_2298, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1867, c_2292])).
% 10.71/3.72  tff(c_2328, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_98, c_1867, c_2298])).
% 10.71/3.72  tff(c_2329, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_2328])).
% 10.71/3.72  tff(c_3100, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_5', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_2508, c_2329])).
% 10.71/3.72  tff(c_2377, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2350])).
% 10.71/3.72  tff(c_2314, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2292])).
% 10.71/3.72  tff(c_2353, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_98, c_50, c_2314])).
% 10.71/3.72  tff(c_2354, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_2353])).
% 10.71/3.72  tff(c_3044, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_2377, c_2354])).
% 10.71/3.72  tff(c_28, plain, (![E_127, C_115, F_129, D_123, B_99, A_67]: (r2_funct_2(u1_struct_0(E_127), u1_struct_0(B_99), k3_tmap_1(A_67, B_99, D_123, E_127, k3_tmap_1(A_67, B_99, C_115, D_123, F_129)), k3_tmap_1(A_67, B_99, C_115, E_127, F_129)) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_115), u1_struct_0(B_99)))) | ~v1_funct_2(F_129, u1_struct_0(C_115), u1_struct_0(B_99)) | ~v1_funct_1(F_129) | ~m1_pre_topc(E_127, D_123) | ~m1_pre_topc(D_123, C_115) | ~m1_pre_topc(E_127, A_67) | v2_struct_0(E_127) | ~m1_pre_topc(D_123, A_67) | v2_struct_0(D_123) | ~m1_pre_topc(C_115, A_67) | v2_struct_0(C_115) | ~l1_pre_topc(B_99) | ~v2_pre_topc(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.71/3.72  tff(c_3056, plain, (![E_127]: (r2_funct_2(u1_struct_0(E_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', E_127, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', E_127, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(E_127, '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc(E_127, '#skF_4') | v2_struct_0(E_127) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3044, c_28])).
% 10.71/3.72  tff(c_3081, plain, (![E_127]: (r2_funct_2(u1_struct_0(E_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', E_127, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', E_127, '#skF_6')) | ~m1_pre_topc(E_127, '#skF_3') | ~m1_pre_topc(E_127, '#skF_4') | v2_struct_0(E_127) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_98, c_66, c_64, c_2709, c_50, c_50, c_46, c_44, c_42, c_3056])).
% 10.71/3.72  tff(c_4010, plain, (![E_504]: (r2_funct_2(u1_struct_0(E_504), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', E_504, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', E_504, '#skF_6')) | ~m1_pre_topc(E_504, '#skF_3') | ~m1_pre_topc(E_504, '#skF_4') | v2_struct_0(E_504))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_62, c_3081])).
% 10.71/3.72  tff(c_4015, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3100, c_4010])).
% 10.71/3.72  tff(c_4024, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_48, c_4015])).
% 10.71/3.72  tff(c_4025, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_4024])).
% 10.71/3.72  tff(c_6602, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6582, c_4025])).
% 10.71/3.72  tff(c_6680, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_133, c_98, c_50, c_1867, c_48, c_6602])).
% 10.71/3.72  tff(c_6681, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_6680])).
% 10.71/3.72  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.71/3.72  tff(c_6732, plain, (k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'))), inference(resolution, [status(thm)], [c_6681, c_4])).
% 10.71/3.72  tff(c_6735, plain, (k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4873, c_2516, c_2513, c_2543, c_6732])).
% 10.71/3.72  tff(c_8410, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_6735])).
% 10.71/3.72  tff(c_8413, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2382, c_8410])).
% 10.71/3.72  tff(c_8416, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8413])).
% 10.71/3.72  tff(c_8418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_8416])).
% 10.71/3.72  tff(c_8419, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_6735])).
% 10.71/3.72  tff(c_8428, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_8419])).
% 10.71/3.72  tff(c_8431, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2378, c_8428])).
% 10.71/3.72  tff(c_8434, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8431])).
% 10.71/3.72  tff(c_8436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_8434])).
% 10.71/3.72  tff(c_8437, plain, (k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_8419])).
% 10.71/3.72  tff(c_2208, plain, (![A_386, B_387, C_388, D_389]: (v5_pre_topc(k2_tmap_1(A_386, B_387, C_388, D_389), D_389, B_387) | ~m1_pre_topc(D_389, A_386) | v2_struct_0(D_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_386), u1_struct_0(B_387)))) | ~v5_pre_topc(C_388, A_386, B_387) | ~v1_funct_2(C_388, u1_struct_0(A_386), u1_struct_0(B_387)) | ~v1_funct_1(C_388) | ~l1_pre_topc(B_387) | ~v2_pre_topc(B_387) | v2_struct_0(B_387) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.71/3.72  tff(c_2212, plain, (![D_389]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_389), D_389, '#skF_2') | ~m1_pre_topc(D_389, '#skF_3') | v2_struct_0(D_389) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2208])).
% 10.71/3.72  tff(c_2221, plain, (![D_389]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_389), D_389, '#skF_2') | ~m1_pre_topc(D_389, '#skF_3') | v2_struct_0(D_389) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_66, c_64, c_40, c_38, c_36, c_2212])).
% 10.71/3.72  tff(c_2222, plain, (![D_389]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_389), D_389, '#skF_2') | ~m1_pre_topc(D_389, '#skF_3') | v2_struct_0(D_389))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_2221])).
% 10.71/3.72  tff(c_2379, plain, (![D_389]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_389), D_389, '#skF_2') | ~m1_pre_topc(D_389, '#skF_3') | v2_struct_0(D_389))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2222])).
% 10.71/3.72  tff(c_8460, plain, (v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8437, c_2379])).
% 10.71/3.72  tff(c_8479, plain, (v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8460])).
% 10.71/3.72  tff(c_8481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2514, c_8479])).
% 10.71/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.71/3.72  
% 10.71/3.72  Inference rules
% 10.71/3.72  ----------------------
% 10.71/3.72  #Ref     : 0
% 10.71/3.72  #Sup     : 1554
% 10.71/3.72  #Fact    : 0
% 10.71/3.72  #Define  : 0
% 10.71/3.72  #Split   : 28
% 10.71/3.72  #Chain   : 0
% 10.71/3.72  #Close   : 0
% 10.71/3.72  
% 10.71/3.72  Ordering : KBO
% 10.71/3.72  
% 10.71/3.72  Simplification rules
% 10.71/3.72  ----------------------
% 10.71/3.72  #Subsume      : 330
% 10.71/3.72  #Demod        : 5799
% 10.71/3.72  #Tautology    : 412
% 10.71/3.72  #SimpNegUnit  : 848
% 10.71/3.72  #BackRed      : 29
% 10.71/3.72  
% 10.71/3.72  #Partial instantiations: 0
% 10.71/3.72  #Strategies tried      : 1
% 10.71/3.72  
% 10.71/3.72  Timing (in seconds)
% 10.71/3.72  ----------------------
% 10.76/3.73  Preprocessing        : 0.37
% 10.76/3.73  Parsing              : 0.19
% 10.76/3.73  CNF conversion       : 0.05
% 10.76/3.73  Main loop            : 2.45
% 10.76/3.73  Inferencing          : 0.62
% 10.76/3.73  Reduction            : 1.08
% 10.76/3.73  Demodulation         : 0.88
% 10.76/3.73  BG Simplification    : 0.08
% 10.76/3.73  Subsumption          : 0.58
% 10.76/3.73  Abstraction          : 0.13
% 10.76/3.73  MUC search           : 0.00
% 10.76/3.73  Cooper               : 0.00
% 10.76/3.73  Total                : 2.89
% 10.76/3.73  Index Insertion      : 0.00
% 10.76/3.73  Index Deletion       : 0.00
% 10.76/3.73  Index Matching       : 0.00
% 10.76/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
