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
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 401 expanded)
%              Number of leaves         :   36 ( 171 expanded)
%              Depth                    :   16
%              Number of atoms          :  482 (3534 expanded)
%              Number of equality atoms :   31 ( 165 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_236,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,D)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_119,axiom,(
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

tff(f_87,axiom,(
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

tff(f_166,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_26,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_20,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_24,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_18,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_22,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_70,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_94,plain,(
    ! [B_443,A_444] :
      ( v2_pre_topc(B_443)
      | ~ m1_pre_topc(B_443,A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_109,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_100])).

tff(c_75,plain,(
    ! [B_441,A_442] :
      ( l1_pre_topc(B_441)
      | ~ m1_pre_topc(B_441,A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_69,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_208,plain,(
    ! [B_455,A_456,C_457] :
      ( m1_connsp_2(B_455,A_456,C_457)
      | ~ r2_hidden(C_457,B_455)
      | ~ v3_pre_topc(B_455,A_456)
      | ~ m1_subset_1(C_457,u1_struct_0(A_456))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_456)))
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    ! [B_455] :
      ( m1_connsp_2(B_455,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_455)
      | ~ v3_pre_topc(B_455,'#skF_4')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_208])).

tff(c_215,plain,(
    ! [B_455] :
      ( m1_connsp_2(B_455,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_455)
      | ~ v3_pre_topc(B_455,'#skF_4')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90,c_210])).

tff(c_221,plain,(
    ! [B_458] :
      ( m1_connsp_2(B_458,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_458)
      | ~ v3_pre_topc(B_458,'#skF_4')
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_215])).

tff(c_224,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_227,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70,c_224])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_115,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_245,plain,(
    ! [C_465,B_467,E_469,A_466,D_468] :
      ( k3_tmap_1(A_466,B_467,C_465,D_468,E_469) = k2_partfun1(u1_struct_0(C_465),u1_struct_0(B_467),E_469,u1_struct_0(D_468))
      | ~ m1_pre_topc(D_468,C_465)
      | ~ m1_subset_1(E_469,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_465),u1_struct_0(B_467))))
      | ~ v1_funct_2(E_469,u1_struct_0(C_465),u1_struct_0(B_467))
      | ~ v1_funct_1(E_469)
      | ~ m1_pre_topc(D_468,A_466)
      | ~ m1_pre_topc(C_465,A_466)
      | ~ l1_pre_topc(B_467)
      | ~ v2_pre_topc(B_467)
      | v2_struct_0(B_467)
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_247,plain,(
    ! [A_466,D_468] :
      ( k3_tmap_1(A_466,'#skF_2','#skF_4',D_468,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_468))
      | ~ m1_pre_topc(D_468,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_468,A_466)
      | ~ m1_pre_topc('#skF_4',A_466)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_34,c_245])).

tff(c_250,plain,(
    ! [A_466,D_468] :
      ( k3_tmap_1(A_466,'#skF_2','#skF_4',D_468,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_468))
      | ~ m1_pre_topc(D_468,'#skF_4')
      | ~ m1_pre_topc(D_468,A_466)
      | ~ m1_pre_topc('#skF_4',A_466)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_247])).

tff(c_253,plain,(
    ! [A_476,D_477] :
      ( k3_tmap_1(A_476,'#skF_2','#skF_4',D_477,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_477))
      | ~ m1_pre_topc(D_477,'#skF_4')
      | ~ m1_pre_topc(D_477,A_476)
      | ~ m1_pre_topc('#skF_4',A_476)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_250])).

tff(c_259,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_253])).

tff(c_272,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_32,c_259])).

tff(c_273,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_272])).

tff(c_229,plain,(
    ! [A_460,B_461,C_462,D_463] :
      ( k2_partfun1(u1_struct_0(A_460),u1_struct_0(B_461),C_462,u1_struct_0(D_463)) = k2_tmap_1(A_460,B_461,C_462,D_463)
      | ~ m1_pre_topc(D_463,A_460)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_460),u1_struct_0(B_461))))
      | ~ v1_funct_2(C_462,u1_struct_0(A_460),u1_struct_0(B_461))
      | ~ v1_funct_1(C_462)
      | ~ l1_pre_topc(B_461)
      | ~ v2_pre_topc(B_461)
      | v2_struct_0(B_461)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_231,plain,(
    ! [D_463] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_463)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_463)
      | ~ m1_pre_topc(D_463,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_229])).

tff(c_234,plain,(
    ! [D_463] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_463)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_463)
      | ~ m1_pre_topc(D_463,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90,c_50,c_48,c_38,c_36,c_231])).

tff(c_235,plain,(
    ! [D_463] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_463)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_463)
      | ~ m1_pre_topc(D_463,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_234])).

tff(c_285,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_235])).

tff(c_292,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_67,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_155,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_67])).

tff(c_297,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_155])).

tff(c_12,plain,(
    ! [A_60,D_172,B_124,C_156,E_180,G_186] :
      ( r1_tmap_1(B_124,A_60,C_156,G_186)
      | ~ r1_tmap_1(D_172,A_60,k2_tmap_1(B_124,A_60,C_156,D_172),G_186)
      | ~ m1_connsp_2(E_180,B_124,G_186)
      | ~ r1_tarski(E_180,u1_struct_0(D_172))
      | ~ m1_subset_1(G_186,u1_struct_0(D_172))
      | ~ m1_subset_1(G_186,u1_struct_0(B_124))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(u1_struct_0(B_124)))
      | ~ m1_pre_topc(D_172,B_124)
      | v2_struct_0(D_172)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_124),u1_struct_0(A_60))))
      | ~ v1_funct_2(C_156,u1_struct_0(B_124),u1_struct_0(A_60))
      | ~ v1_funct_1(C_156)
      | ~ l1_pre_topc(B_124)
      | ~ v2_pre_topc(B_124)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_304,plain,(
    ! [E_180] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_180,'#skF_4','#skF_8')
      | ~ r1_tarski(E_180,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_297,c_12])).

tff(c_307,plain,(
    ! [E_180] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_180,'#skF_4','#skF_8')
      | ~ r1_tarski(E_180,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_109,c_90,c_38,c_36,c_34,c_32,c_69,c_26,c_304])).

tff(c_326,plain,(
    ! [E_478] :
      ( ~ m1_connsp_2(E_478,'#skF_4','#skF_8')
      | ~ r1_tarski(E_478,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_478,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_115,c_307])).

tff(c_329,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_326])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_227,c_329])).

tff(c_335,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_429,plain,(
    ! [B_489,A_490,C_491] :
      ( m1_connsp_2(B_489,A_490,C_491)
      | ~ r2_hidden(C_491,B_489)
      | ~ v3_pre_topc(B_489,A_490)
      | ~ m1_subset_1(C_491,u1_struct_0(A_490))
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_431,plain,(
    ! [B_489] :
      ( m1_connsp_2(B_489,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_489)
      | ~ v3_pre_topc(B_489,'#skF_4')
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_429])).

tff(c_436,plain,(
    ! [B_489] :
      ( m1_connsp_2(B_489,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_489)
      | ~ v3_pre_topc(B_489,'#skF_4')
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90,c_431])).

tff(c_449,plain,(
    ! [B_496] :
      ( m1_connsp_2(B_496,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_496)
      | ~ v3_pre_topc(B_496,'#skF_4')
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_436])).

tff(c_452,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_449])).

tff(c_455,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70,c_452])).

tff(c_553,plain,(
    ! [C_517,E_516,B_514,G_518,D_513,A_515] :
      ( r1_tmap_1(D_513,A_515,k2_tmap_1(B_514,A_515,C_517,D_513),G_518)
      | ~ r1_tmap_1(B_514,A_515,C_517,G_518)
      | ~ m1_connsp_2(E_516,B_514,G_518)
      | ~ r1_tarski(E_516,u1_struct_0(D_513))
      | ~ m1_subset_1(G_518,u1_struct_0(D_513))
      | ~ m1_subset_1(G_518,u1_struct_0(B_514))
      | ~ m1_subset_1(E_516,k1_zfmisc_1(u1_struct_0(B_514)))
      | ~ m1_pre_topc(D_513,B_514)
      | v2_struct_0(D_513)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_514),u1_struct_0(A_515))))
      | ~ v1_funct_2(C_517,u1_struct_0(B_514),u1_struct_0(A_515))
      | ~ v1_funct_1(C_517)
      | ~ l1_pre_topc(B_514)
      | ~ v2_pre_topc(B_514)
      | v2_struct_0(B_514)
      | ~ l1_pre_topc(A_515)
      | ~ v2_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_555,plain,(
    ! [D_513,A_515,C_517] :
      ( r1_tmap_1(D_513,A_515,k2_tmap_1('#skF_4',A_515,C_517,D_513),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_515,C_517,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_513))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_513))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_513,'#skF_4')
      | v2_struct_0(D_513)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_515))))
      | ~ v1_funct_2(C_517,u1_struct_0('#skF_4'),u1_struct_0(A_515))
      | ~ v1_funct_1(C_517)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_515)
      | ~ v2_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_455,c_553])).

tff(c_558,plain,(
    ! [D_513,A_515,C_517] :
      ( r1_tmap_1(D_513,A_515,k2_tmap_1('#skF_4',A_515,C_517,D_513),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_515,C_517,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_513))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_513))
      | ~ m1_pre_topc(D_513,'#skF_4')
      | v2_struct_0(D_513)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_515))))
      | ~ v1_funct_2(C_517,u1_struct_0('#skF_4'),u1_struct_0(A_515))
      | ~ v1_funct_1(C_517)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_515)
      | ~ v2_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90,c_30,c_69,c_555])).

tff(c_560,plain,(
    ! [D_519,A_520,C_521] :
      ( r1_tmap_1(D_519,A_520,k2_tmap_1('#skF_4',A_520,C_521,D_519),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_520,C_521,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_519))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_519))
      | ~ m1_pre_topc(D_519,'#skF_4')
      | v2_struct_0(D_519)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_520))))
      | ~ v1_funct_2(C_521,u1_struct_0('#skF_4'),u1_struct_0(A_520))
      | ~ v1_funct_1(C_521)
      | ~ l1_pre_topc(A_520)
      | ~ v2_pre_topc(A_520)
      | v2_struct_0(A_520) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_558])).

tff(c_562,plain,(
    ! [D_519] :
      ( r1_tmap_1(D_519,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_519),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_519))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_519))
      | ~ m1_pre_topc(D_519,'#skF_4')
      | v2_struct_0(D_519)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_560])).

tff(c_565,plain,(
    ! [D_519] :
      ( r1_tmap_1(D_519,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_519),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_519))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_519))
      | ~ m1_pre_topc(D_519,'#skF_4')
      | v2_struct_0(D_519)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_335,c_562])).

tff(c_567,plain,(
    ! [D_522] :
      ( r1_tmap_1(D_522,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_522),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_522))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_522))
      | ~ m1_pre_topc(D_522,'#skF_4')
      | v2_struct_0(D_522) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_565])).

tff(c_466,plain,(
    ! [E_503,B_501,C_499,D_502,A_500] :
      ( k3_tmap_1(A_500,B_501,C_499,D_502,E_503) = k2_partfun1(u1_struct_0(C_499),u1_struct_0(B_501),E_503,u1_struct_0(D_502))
      | ~ m1_pre_topc(D_502,C_499)
      | ~ m1_subset_1(E_503,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_499),u1_struct_0(B_501))))
      | ~ v1_funct_2(E_503,u1_struct_0(C_499),u1_struct_0(B_501))
      | ~ v1_funct_1(E_503)
      | ~ m1_pre_topc(D_502,A_500)
      | ~ m1_pre_topc(C_499,A_500)
      | ~ l1_pre_topc(B_501)
      | ~ v2_pre_topc(B_501)
      | v2_struct_0(B_501)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_468,plain,(
    ! [A_500,D_502] :
      ( k3_tmap_1(A_500,'#skF_2','#skF_4',D_502,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_502))
      | ~ m1_pre_topc(D_502,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_502,A_500)
      | ~ m1_pre_topc('#skF_4',A_500)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_34,c_466])).

tff(c_471,plain,(
    ! [A_500,D_502] :
      ( k3_tmap_1(A_500,'#skF_2','#skF_4',D_502,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_502))
      | ~ m1_pre_topc(D_502,'#skF_4')
      | ~ m1_pre_topc(D_502,A_500)
      | ~ m1_pre_topc('#skF_4',A_500)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_468])).

tff(c_473,plain,(
    ! [A_504,D_505] :
      ( k3_tmap_1(A_504,'#skF_2','#skF_4',D_505,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_pre_topc(D_505,A_504)
      | ~ m1_pre_topc('#skF_4',A_504)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_471])).

tff(c_479,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_473])).

tff(c_492,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_32,c_479])).

tff(c_493,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_492])).

tff(c_442,plain,(
    ! [A_492,B_493,C_494,D_495] :
      ( k2_partfun1(u1_struct_0(A_492),u1_struct_0(B_493),C_494,u1_struct_0(D_495)) = k2_tmap_1(A_492,B_493,C_494,D_495)
      | ~ m1_pre_topc(D_495,A_492)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_492),u1_struct_0(B_493))))
      | ~ v1_funct_2(C_494,u1_struct_0(A_492),u1_struct_0(B_493))
      | ~ v1_funct_1(C_494)
      | ~ l1_pre_topc(B_493)
      | ~ v2_pre_topc(B_493)
      | v2_struct_0(B_493)
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_444,plain,(
    ! [D_495] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_495)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_495)
      | ~ m1_pre_topc(D_495,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_442])).

tff(c_447,plain,(
    ! [D_495] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_495)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_495)
      | ~ m1_pre_topc(D_495,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90,c_50,c_48,c_38,c_36,c_444])).

tff(c_448,plain,(
    ! [D_495] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_495)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_495)
      | ~ m1_pre_topc(D_495,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_447])).

tff(c_505,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_448])).

tff(c_512,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_505])).

tff(c_334,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_517,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_334])).

tff(c_572,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_567,c_517])).

tff(c_579,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_20,c_572])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.53  
% 3.60/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.53  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.60/1.53  
% 3.60/1.53  %Foreground sorts:
% 3.60/1.53  
% 3.60/1.53  
% 3.60/1.53  %Background operators:
% 3.60/1.53  
% 3.60/1.53  
% 3.60/1.53  %Foreground operators:
% 3.60/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.60/1.53  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.60/1.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.60/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.60/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.60/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.60/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.60/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.60/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.60/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.60/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.60/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.53  
% 3.66/1.56  tff(f_236, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.66/1.56  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.66/1.56  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.66/1.56  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.66/1.56  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.66/1.56  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.66/1.56  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.66/1.56  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_26, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_20, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_24, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_18, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_22, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_70, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 3.66/1.56  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_94, plain, (![B_443, A_444]: (v2_pre_topc(B_443) | ~m1_pre_topc(B_443, A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.66/1.56  tff(c_100, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_94])).
% 3.66/1.56  tff(c_109, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_100])).
% 3.66/1.56  tff(c_75, plain, (![B_441, A_442]: (l1_pre_topc(B_441) | ~m1_pre_topc(B_441, A_442) | ~l1_pre_topc(A_442))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.56  tff(c_81, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.66/1.56  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_81])).
% 3.66/1.56  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_69, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 3.66/1.56  tff(c_208, plain, (![B_455, A_456, C_457]: (m1_connsp_2(B_455, A_456, C_457) | ~r2_hidden(C_457, B_455) | ~v3_pre_topc(B_455, A_456) | ~m1_subset_1(C_457, u1_struct_0(A_456)) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_456))) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.66/1.56  tff(c_210, plain, (![B_455]: (m1_connsp_2(B_455, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_455) | ~v3_pre_topc(B_455, '#skF_4') | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_69, c_208])).
% 3.66/1.56  tff(c_215, plain, (![B_455]: (m1_connsp_2(B_455, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_455) | ~v3_pre_topc(B_455, '#skF_4') | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90, c_210])).
% 3.66/1.56  tff(c_221, plain, (![B_458]: (m1_connsp_2(B_458, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_458) | ~v3_pre_topc(B_458, '#skF_4') | ~m1_subset_1(B_458, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_215])).
% 3.66/1.56  tff(c_224, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_221])).
% 3.66/1.56  tff(c_227, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_70, c_224])).
% 3.66/1.56  tff(c_60, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_68, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 3.66/1.56  tff(c_115, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 3.66/1.56  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_245, plain, (![C_465, B_467, E_469, A_466, D_468]: (k3_tmap_1(A_466, B_467, C_465, D_468, E_469)=k2_partfun1(u1_struct_0(C_465), u1_struct_0(B_467), E_469, u1_struct_0(D_468)) | ~m1_pre_topc(D_468, C_465) | ~m1_subset_1(E_469, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_465), u1_struct_0(B_467)))) | ~v1_funct_2(E_469, u1_struct_0(C_465), u1_struct_0(B_467)) | ~v1_funct_1(E_469) | ~m1_pre_topc(D_468, A_466) | ~m1_pre_topc(C_465, A_466) | ~l1_pre_topc(B_467) | ~v2_pre_topc(B_467) | v2_struct_0(B_467) | ~l1_pre_topc(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.66/1.56  tff(c_247, plain, (![A_466, D_468]: (k3_tmap_1(A_466, '#skF_2', '#skF_4', D_468, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_468)) | ~m1_pre_topc(D_468, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_468, A_466) | ~m1_pre_topc('#skF_4', A_466) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(resolution, [status(thm)], [c_34, c_245])).
% 3.66/1.56  tff(c_250, plain, (![A_466, D_468]: (k3_tmap_1(A_466, '#skF_2', '#skF_4', D_468, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_468)) | ~m1_pre_topc(D_468, '#skF_4') | ~m1_pre_topc(D_468, A_466) | ~m1_pre_topc('#skF_4', A_466) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_247])).
% 3.66/1.56  tff(c_253, plain, (![A_476, D_477]: (k3_tmap_1(A_476, '#skF_2', '#skF_4', D_477, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_477)) | ~m1_pre_topc(D_477, '#skF_4') | ~m1_pre_topc(D_477, A_476) | ~m1_pre_topc('#skF_4', A_476) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(negUnitSimplification, [status(thm)], [c_52, c_250])).
% 3.66/1.56  tff(c_259, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_253])).
% 3.66/1.56  tff(c_272, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_32, c_259])).
% 3.66/1.56  tff(c_273, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_272])).
% 3.66/1.56  tff(c_229, plain, (![A_460, B_461, C_462, D_463]: (k2_partfun1(u1_struct_0(A_460), u1_struct_0(B_461), C_462, u1_struct_0(D_463))=k2_tmap_1(A_460, B_461, C_462, D_463) | ~m1_pre_topc(D_463, A_460) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_460), u1_struct_0(B_461)))) | ~v1_funct_2(C_462, u1_struct_0(A_460), u1_struct_0(B_461)) | ~v1_funct_1(C_462) | ~l1_pre_topc(B_461) | ~v2_pre_topc(B_461) | v2_struct_0(B_461) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.66/1.56  tff(c_231, plain, (![D_463]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_463))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_463) | ~m1_pre_topc(D_463, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_229])).
% 3.66/1.56  tff(c_234, plain, (![D_463]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_463))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_463) | ~m1_pre_topc(D_463, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90, c_50, c_48, c_38, c_36, c_231])).
% 3.66/1.56  tff(c_235, plain, (![D_463]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_463))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_463) | ~m1_pre_topc(D_463, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_234])).
% 3.66/1.56  tff(c_285, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_273, c_235])).
% 3.66/1.56  tff(c_292, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_285])).
% 3.66/1.56  tff(c_66, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.66/1.56  tff(c_67, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 3.66/1.56  tff(c_155, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_115, c_67])).
% 3.66/1.56  tff(c_297, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_155])).
% 3.66/1.56  tff(c_12, plain, (![A_60, D_172, B_124, C_156, E_180, G_186]: (r1_tmap_1(B_124, A_60, C_156, G_186) | ~r1_tmap_1(D_172, A_60, k2_tmap_1(B_124, A_60, C_156, D_172), G_186) | ~m1_connsp_2(E_180, B_124, G_186) | ~r1_tarski(E_180, u1_struct_0(D_172)) | ~m1_subset_1(G_186, u1_struct_0(D_172)) | ~m1_subset_1(G_186, u1_struct_0(B_124)) | ~m1_subset_1(E_180, k1_zfmisc_1(u1_struct_0(B_124))) | ~m1_pre_topc(D_172, B_124) | v2_struct_0(D_172) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_124), u1_struct_0(A_60)))) | ~v1_funct_2(C_156, u1_struct_0(B_124), u1_struct_0(A_60)) | ~v1_funct_1(C_156) | ~l1_pre_topc(B_124) | ~v2_pre_topc(B_124) | v2_struct_0(B_124) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.66/1.56  tff(c_304, plain, (![E_180]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_180, '#skF_4', '#skF_8') | ~r1_tarski(E_180, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_180, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_297, c_12])).
% 3.66/1.56  tff(c_307, plain, (![E_180]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_180, '#skF_4', '#skF_8') | ~r1_tarski(E_180, u1_struct_0('#skF_3')) | ~m1_subset_1(E_180, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_109, c_90, c_38, c_36, c_34, c_32, c_69, c_26, c_304])).
% 3.66/1.56  tff(c_326, plain, (![E_478]: (~m1_connsp_2(E_478, '#skF_4', '#skF_8') | ~r1_tarski(E_478, u1_struct_0('#skF_3')) | ~m1_subset_1(E_478, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_115, c_307])).
% 3.66/1.56  tff(c_329, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_326])).
% 3.66/1.56  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_227, c_329])).
% 3.66/1.56  tff(c_335, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 3.66/1.56  tff(c_429, plain, (![B_489, A_490, C_491]: (m1_connsp_2(B_489, A_490, C_491) | ~r2_hidden(C_491, B_489) | ~v3_pre_topc(B_489, A_490) | ~m1_subset_1(C_491, u1_struct_0(A_490)) | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0(A_490))) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.66/1.56  tff(c_431, plain, (![B_489]: (m1_connsp_2(B_489, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_489) | ~v3_pre_topc(B_489, '#skF_4') | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_69, c_429])).
% 3.66/1.56  tff(c_436, plain, (![B_489]: (m1_connsp_2(B_489, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_489) | ~v3_pre_topc(B_489, '#skF_4') | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90, c_431])).
% 3.66/1.56  tff(c_449, plain, (![B_496]: (m1_connsp_2(B_496, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_496) | ~v3_pre_topc(B_496, '#skF_4') | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_436])).
% 3.66/1.56  tff(c_452, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_449])).
% 3.66/1.56  tff(c_455, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_70, c_452])).
% 3.66/1.56  tff(c_553, plain, (![C_517, E_516, B_514, G_518, D_513, A_515]: (r1_tmap_1(D_513, A_515, k2_tmap_1(B_514, A_515, C_517, D_513), G_518) | ~r1_tmap_1(B_514, A_515, C_517, G_518) | ~m1_connsp_2(E_516, B_514, G_518) | ~r1_tarski(E_516, u1_struct_0(D_513)) | ~m1_subset_1(G_518, u1_struct_0(D_513)) | ~m1_subset_1(G_518, u1_struct_0(B_514)) | ~m1_subset_1(E_516, k1_zfmisc_1(u1_struct_0(B_514))) | ~m1_pre_topc(D_513, B_514) | v2_struct_0(D_513) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_514), u1_struct_0(A_515)))) | ~v1_funct_2(C_517, u1_struct_0(B_514), u1_struct_0(A_515)) | ~v1_funct_1(C_517) | ~l1_pre_topc(B_514) | ~v2_pre_topc(B_514) | v2_struct_0(B_514) | ~l1_pre_topc(A_515) | ~v2_pre_topc(A_515) | v2_struct_0(A_515))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.66/1.56  tff(c_555, plain, (![D_513, A_515, C_517]: (r1_tmap_1(D_513, A_515, k2_tmap_1('#skF_4', A_515, C_517, D_513), '#skF_8') | ~r1_tmap_1('#skF_4', A_515, C_517, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_513)) | ~m1_subset_1('#skF_8', u1_struct_0(D_513)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_513, '#skF_4') | v2_struct_0(D_513) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_515)))) | ~v1_funct_2(C_517, u1_struct_0('#skF_4'), u1_struct_0(A_515)) | ~v1_funct_1(C_517) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_515) | ~v2_pre_topc(A_515) | v2_struct_0(A_515))), inference(resolution, [status(thm)], [c_455, c_553])).
% 3.66/1.56  tff(c_558, plain, (![D_513, A_515, C_517]: (r1_tmap_1(D_513, A_515, k2_tmap_1('#skF_4', A_515, C_517, D_513), '#skF_8') | ~r1_tmap_1('#skF_4', A_515, C_517, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_513)) | ~m1_subset_1('#skF_8', u1_struct_0(D_513)) | ~m1_pre_topc(D_513, '#skF_4') | v2_struct_0(D_513) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_515)))) | ~v1_funct_2(C_517, u1_struct_0('#skF_4'), u1_struct_0(A_515)) | ~v1_funct_1(C_517) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_515) | ~v2_pre_topc(A_515) | v2_struct_0(A_515))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90, c_30, c_69, c_555])).
% 3.66/1.56  tff(c_560, plain, (![D_519, A_520, C_521]: (r1_tmap_1(D_519, A_520, k2_tmap_1('#skF_4', A_520, C_521, D_519), '#skF_8') | ~r1_tmap_1('#skF_4', A_520, C_521, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_519)) | ~m1_subset_1('#skF_8', u1_struct_0(D_519)) | ~m1_pre_topc(D_519, '#skF_4') | v2_struct_0(D_519) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_520)))) | ~v1_funct_2(C_521, u1_struct_0('#skF_4'), u1_struct_0(A_520)) | ~v1_funct_1(C_521) | ~l1_pre_topc(A_520) | ~v2_pre_topc(A_520) | v2_struct_0(A_520))), inference(negUnitSimplification, [status(thm)], [c_42, c_558])).
% 3.66/1.56  tff(c_562, plain, (![D_519]: (r1_tmap_1(D_519, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_519), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_519)) | ~m1_subset_1('#skF_8', u1_struct_0(D_519)) | ~m1_pre_topc(D_519, '#skF_4') | v2_struct_0(D_519) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_560])).
% 3.66/1.56  tff(c_565, plain, (![D_519]: (r1_tmap_1(D_519, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_519), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_519)) | ~m1_subset_1('#skF_8', u1_struct_0(D_519)) | ~m1_pre_topc(D_519, '#skF_4') | v2_struct_0(D_519) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_335, c_562])).
% 3.66/1.56  tff(c_567, plain, (![D_522]: (r1_tmap_1(D_522, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_522), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_522)) | ~m1_subset_1('#skF_8', u1_struct_0(D_522)) | ~m1_pre_topc(D_522, '#skF_4') | v2_struct_0(D_522))), inference(negUnitSimplification, [status(thm)], [c_52, c_565])).
% 3.66/1.56  tff(c_466, plain, (![E_503, B_501, C_499, D_502, A_500]: (k3_tmap_1(A_500, B_501, C_499, D_502, E_503)=k2_partfun1(u1_struct_0(C_499), u1_struct_0(B_501), E_503, u1_struct_0(D_502)) | ~m1_pre_topc(D_502, C_499) | ~m1_subset_1(E_503, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_499), u1_struct_0(B_501)))) | ~v1_funct_2(E_503, u1_struct_0(C_499), u1_struct_0(B_501)) | ~v1_funct_1(E_503) | ~m1_pre_topc(D_502, A_500) | ~m1_pre_topc(C_499, A_500) | ~l1_pre_topc(B_501) | ~v2_pre_topc(B_501) | v2_struct_0(B_501) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.66/1.56  tff(c_468, plain, (![A_500, D_502]: (k3_tmap_1(A_500, '#skF_2', '#skF_4', D_502, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_502)) | ~m1_pre_topc(D_502, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_502, A_500) | ~m1_pre_topc('#skF_4', A_500) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_34, c_466])).
% 3.66/1.56  tff(c_471, plain, (![A_500, D_502]: (k3_tmap_1(A_500, '#skF_2', '#skF_4', D_502, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_502)) | ~m1_pre_topc(D_502, '#skF_4') | ~m1_pre_topc(D_502, A_500) | ~m1_pre_topc('#skF_4', A_500) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_468])).
% 3.66/1.56  tff(c_473, plain, (![A_504, D_505]: (k3_tmap_1(A_504, '#skF_2', '#skF_4', D_505, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_505)) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_pre_topc(D_505, A_504) | ~m1_pre_topc('#skF_4', A_504) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(negUnitSimplification, [status(thm)], [c_52, c_471])).
% 3.66/1.56  tff(c_479, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_473])).
% 3.66/1.56  tff(c_492, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_32, c_479])).
% 3.66/1.56  tff(c_493, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_492])).
% 3.66/1.56  tff(c_442, plain, (![A_492, B_493, C_494, D_495]: (k2_partfun1(u1_struct_0(A_492), u1_struct_0(B_493), C_494, u1_struct_0(D_495))=k2_tmap_1(A_492, B_493, C_494, D_495) | ~m1_pre_topc(D_495, A_492) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_492), u1_struct_0(B_493)))) | ~v1_funct_2(C_494, u1_struct_0(A_492), u1_struct_0(B_493)) | ~v1_funct_1(C_494) | ~l1_pre_topc(B_493) | ~v2_pre_topc(B_493) | v2_struct_0(B_493) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.66/1.56  tff(c_444, plain, (![D_495]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_495))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_495) | ~m1_pre_topc(D_495, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_442])).
% 3.66/1.56  tff(c_447, plain, (![D_495]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_495))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_495) | ~m1_pre_topc(D_495, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90, c_50, c_48, c_38, c_36, c_444])).
% 3.66/1.56  tff(c_448, plain, (![D_495]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_495))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_495) | ~m1_pre_topc(D_495, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_447])).
% 3.66/1.56  tff(c_505, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_493, c_448])).
% 3.66/1.56  tff(c_512, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_505])).
% 3.66/1.56  tff(c_334, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 3.66/1.56  tff(c_517, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_334])).
% 3.66/1.56  tff(c_572, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_567, c_517])).
% 3.66/1.56  tff(c_579, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_20, c_572])).
% 3.66/1.56  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_579])).
% 3.66/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.56  
% 3.66/1.56  Inference rules
% 3.66/1.56  ----------------------
% 3.66/1.56  #Ref     : 0
% 3.66/1.56  #Sup     : 97
% 3.66/1.56  #Fact    : 0
% 3.66/1.56  #Define  : 0
% 3.66/1.56  #Split   : 4
% 3.66/1.56  #Chain   : 0
% 3.66/1.56  #Close   : 0
% 3.66/1.56  
% 3.66/1.56  Ordering : KBO
% 3.66/1.56  
% 3.66/1.56  Simplification rules
% 3.66/1.56  ----------------------
% 3.66/1.56  #Subsume      : 10
% 3.66/1.56  #Demod        : 209
% 3.66/1.56  #Tautology    : 51
% 3.66/1.56  #SimpNegUnit  : 22
% 3.66/1.56  #BackRed      : 4
% 3.66/1.56  
% 3.66/1.56  #Partial instantiations: 0
% 3.66/1.56  #Strategies tried      : 1
% 3.66/1.56  
% 3.66/1.56  Timing (in seconds)
% 3.66/1.56  ----------------------
% 3.66/1.56  Preprocessing        : 0.42
% 3.66/1.56  Parsing              : 0.21
% 3.66/1.56  CNF conversion       : 0.06
% 3.66/1.56  Main loop            : 0.36
% 3.66/1.56  Inferencing          : 0.13
% 3.66/1.56  Reduction            : 0.12
% 3.66/1.56  Demodulation         : 0.09
% 3.66/1.56  BG Simplification    : 0.02
% 3.66/1.56  Subsumption          : 0.07
% 3.66/1.57  Abstraction          : 0.02
% 3.66/1.57  MUC search           : 0.00
% 3.66/1.57  Cooper               : 0.00
% 3.66/1.57  Total                : 0.85
% 3.66/1.57  Index Insertion      : 0.00
% 3.66/1.57  Index Deletion       : 0.00
% 3.66/1.57  Index Matching       : 0.00
% 3.66/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
