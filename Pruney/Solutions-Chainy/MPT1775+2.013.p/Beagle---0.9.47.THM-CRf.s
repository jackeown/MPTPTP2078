%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 306 expanded)
%              Number of leaves         :   31 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  364 (2455 expanded)
%              Number of equality atoms :   31 ( 135 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(f_193,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

tff(f_142,axiom,(
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
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_22,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_18,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_14,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_16,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_102,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_83,plain,(
    ! [B_238,A_239] :
      ( v2_pre_topc(B_238)
      | ~ m1_pre_topc(B_238,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_83])).

tff(c_95,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_86])).

tff(c_64,plain,(
    ! [B_236,A_237] :
      ( l1_pre_topc(B_236)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_67])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_26,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_122,plain,(
    ! [C_249,A_246,D_245,B_247,E_248] :
      ( k3_tmap_1(A_246,B_247,C_249,D_245,E_248) = k2_partfun1(u1_struct_0(C_249),u1_struct_0(B_247),E_248,u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,C_249)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249),u1_struct_0(B_247))))
      | ~ v1_funct_2(E_248,u1_struct_0(C_249),u1_struct_0(B_247))
      | ~ v1_funct_1(E_248)
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc(C_249,A_246)
      | ~ l1_pre_topc(B_247)
      | ~ v2_pre_topc(B_247)
      | v2_struct_0(B_247)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_124,plain,(
    ! [A_246,D_245] :
      ( k3_tmap_1(A_246,'#skF_2','#skF_4',D_245,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc('#skF_4',A_246)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_127,plain,(
    ! [A_246,D_245] :
      ( k3_tmap_1(A_246,'#skF_2','#skF_4',D_245,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,'#skF_4')
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc('#skF_4',A_246)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_124])).

tff(c_129,plain,(
    ! [A_250,D_251] :
      ( k3_tmap_1(A_250,'#skF_2','#skF_4',D_251,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_251))
      | ~ m1_pre_topc(D_251,'#skF_4')
      | ~ m1_pre_topc(D_251,A_250)
      | ~ m1_pre_topc('#skF_4',A_250)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_127])).

tff(c_135,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_129])).

tff(c_146,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_30,c_20,c_135])).

tff(c_147,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_146])).

tff(c_106,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( k2_partfun1(u1_struct_0(A_240),u1_struct_0(B_241),C_242,u1_struct_0(D_243)) = k2_tmap_1(A_240,B_241,C_242,D_243)
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0(B_241))))
      | ~ v1_funct_2(C_242,u1_struct_0(A_240),u1_struct_0(B_241))
      | ~ v1_funct_1(C_242)
      | ~ l1_pre_topc(B_241)
      | ~ v2_pre_topc(B_241)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_111,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_76,c_40,c_38,c_28,c_26,c_108])).

tff(c_112,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_42,c_111])).

tff(c_151,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_112])).

tff(c_158,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_56,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_57,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_105,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_57])).

tff(c_163,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_105])).

tff(c_195,plain,(
    ! [B_261,F_260,A_259,D_263,C_262] :
      ( r1_tmap_1(B_261,A_259,C_262,F_260)
      | ~ r1_tmap_1(D_263,A_259,k2_tmap_1(B_261,A_259,C_262,D_263),F_260)
      | ~ m1_subset_1(F_260,u1_struct_0(D_263))
      | ~ m1_subset_1(F_260,u1_struct_0(B_261))
      | ~ m1_pre_topc(D_263,B_261)
      | ~ v1_tsep_1(D_263,B_261)
      | v2_struct_0(D_263)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_261),u1_struct_0(A_259))))
      | ~ v1_funct_2(C_262,u1_struct_0(B_261),u1_struct_0(A_259))
      | ~ v1_funct_1(C_262)
      | ~ l1_pre_topc(B_261)
      | ~ v2_pre_topc(B_261)
      | v2_struct_0(B_261)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_199,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_195])).

tff(c_206,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_95,c_76,c_28,c_26,c_24,c_22,c_20,c_18,c_59,c_199])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_32,c_36,c_102,c_206])).

tff(c_210,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_298,plain,(
    ! [D_285,F_282,C_284,B_283,A_281] :
      ( r1_tmap_1(D_285,A_281,k2_tmap_1(B_283,A_281,C_284,D_285),F_282)
      | ~ r1_tmap_1(B_283,A_281,C_284,F_282)
      | ~ m1_subset_1(F_282,u1_struct_0(D_285))
      | ~ m1_subset_1(F_282,u1_struct_0(B_283))
      | ~ m1_pre_topc(D_285,B_283)
      | ~ v1_tsep_1(D_285,B_283)
      | v2_struct_0(D_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_283),u1_struct_0(A_281))))
      | ~ v1_funct_2(C_284,u1_struct_0(B_283),u1_struct_0(A_281))
      | ~ v1_funct_1(C_284)
      | ~ l1_pre_topc(B_283)
      | ~ v2_pre_topc(B_283)
      | v2_struct_0(B_283)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_300,plain,(
    ! [D_285,F_282] :
      ( r1_tmap_1(D_285,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_285),F_282)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_282)
      | ~ m1_subset_1(F_282,u1_struct_0(D_285))
      | ~ m1_subset_1(F_282,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_285,'#skF_4')
      | ~ v1_tsep_1(D_285,'#skF_4')
      | v2_struct_0(D_285)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_298])).

tff(c_303,plain,(
    ! [D_285,F_282] :
      ( r1_tmap_1(D_285,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_285),F_282)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_282)
      | ~ m1_subset_1(F_282,u1_struct_0(D_285))
      | ~ m1_subset_1(F_282,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_285,'#skF_4')
      | ~ v1_tsep_1(D_285,'#skF_4')
      | v2_struct_0(D_285)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_95,c_76,c_28,c_26,c_300])).

tff(c_305,plain,(
    ! [D_286,F_287] :
      ( r1_tmap_1(D_286,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_286),F_287)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_287)
      | ~ m1_subset_1(F_287,u1_struct_0(D_286))
      | ~ m1_subset_1(F_287,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ v1_tsep_1(D_286,'#skF_4')
      | v2_struct_0(D_286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_32,c_303])).

tff(c_231,plain,(
    ! [C_273,D_269,E_272,A_270,B_271] :
      ( k3_tmap_1(A_270,B_271,C_273,D_269,E_272) = k2_partfun1(u1_struct_0(C_273),u1_struct_0(B_271),E_272,u1_struct_0(D_269))
      | ~ m1_pre_topc(D_269,C_273)
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_273),u1_struct_0(B_271))))
      | ~ v1_funct_2(E_272,u1_struct_0(C_273),u1_struct_0(B_271))
      | ~ v1_funct_1(E_272)
      | ~ m1_pre_topc(D_269,A_270)
      | ~ m1_pre_topc(C_273,A_270)
      | ~ l1_pre_topc(B_271)
      | ~ v2_pre_topc(B_271)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_233,plain,(
    ! [A_270,D_269] :
      ( k3_tmap_1(A_270,'#skF_2','#skF_4',D_269,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_269))
      | ~ m1_pre_topc(D_269,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_269,A_270)
      | ~ m1_pre_topc('#skF_4',A_270)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_24,c_231])).

tff(c_236,plain,(
    ! [A_270,D_269] :
      ( k3_tmap_1(A_270,'#skF_2','#skF_4',D_269,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_269))
      | ~ m1_pre_topc(D_269,'#skF_4')
      | ~ m1_pre_topc(D_269,A_270)
      | ~ m1_pre_topc('#skF_4',A_270)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_233])).

tff(c_238,plain,(
    ! [A_274,D_275] :
      ( k3_tmap_1(A_274,'#skF_2','#skF_4',D_275,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_275))
      | ~ m1_pre_topc(D_275,'#skF_4')
      | ~ m1_pre_topc(D_275,A_274)
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_236])).

tff(c_244,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_238])).

tff(c_255,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_30,c_20,c_244])).

tff(c_256,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_255])).

tff(c_215,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k2_partfun1(u1_struct_0(A_264),u1_struct_0(B_265),C_266,u1_struct_0(D_267)) = k2_tmap_1(A_264,B_265,C_266,D_267)
      | ~ m1_pre_topc(D_267,A_264)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_264),u1_struct_0(B_265))))
      | ~ v1_funct_2(C_266,u1_struct_0(A_264),u1_struct_0(B_265))
      | ~ v1_funct_1(C_266)
      | ~ l1_pre_topc(B_265)
      | ~ v2_pre_topc(B_265)
      | v2_struct_0(B_265)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_217,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_215])).

tff(c_220,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_76,c_40,c_38,c_28,c_26,c_217])).

tff(c_221,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_42,c_220])).

tff(c_260,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_221])).

tff(c_267,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_260])).

tff(c_209,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_272,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_209])).

tff(c_310,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_272])).

tff(c_317,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_59,c_210,c_310])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.40  
% 2.87/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.40  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.40  
% 2.87/1.40  %Foreground sorts:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Background operators:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Foreground operators:
% 2.87/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.40  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.40  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.87/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.40  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.87/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.87/1.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.87/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.87/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.40  
% 2.87/1.43  tff(f_193, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 2.87/1.43  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.87/1.43  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.87/1.43  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.87/1.43  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.87/1.43  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 2.87/1.43  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_22, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_18, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_14, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_16, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_59, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.87/1.43  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_50, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_58, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 2.87/1.43  tff(c_102, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.87/1.43  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_83, plain, (![B_238, A_239]: (v2_pre_topc(B_238) | ~m1_pre_topc(B_238, A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.87/1.43  tff(c_86, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_83])).
% 2.87/1.43  tff(c_95, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_86])).
% 2.87/1.43  tff(c_64, plain, (![B_236, A_237]: (l1_pre_topc(B_236) | ~m1_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.43  tff(c_67, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_64])).
% 2.87/1.43  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_67])).
% 2.87/1.43  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_26, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_122, plain, (![C_249, A_246, D_245, B_247, E_248]: (k3_tmap_1(A_246, B_247, C_249, D_245, E_248)=k2_partfun1(u1_struct_0(C_249), u1_struct_0(B_247), E_248, u1_struct_0(D_245)) | ~m1_pre_topc(D_245, C_249) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249), u1_struct_0(B_247)))) | ~v1_funct_2(E_248, u1_struct_0(C_249), u1_struct_0(B_247)) | ~v1_funct_1(E_248) | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc(C_249, A_246) | ~l1_pre_topc(B_247) | ~v2_pre_topc(B_247) | v2_struct_0(B_247) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.43  tff(c_124, plain, (![A_246, D_245]: (k3_tmap_1(A_246, '#skF_2', '#skF_4', D_245, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_245)) | ~m1_pre_topc(D_245, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc('#skF_4', A_246) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(resolution, [status(thm)], [c_24, c_122])).
% 2.87/1.43  tff(c_127, plain, (![A_246, D_245]: (k3_tmap_1(A_246, '#skF_2', '#skF_4', D_245, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_245)) | ~m1_pre_topc(D_245, '#skF_4') | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc('#skF_4', A_246) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_124])).
% 2.87/1.43  tff(c_129, plain, (![A_250, D_251]: (k3_tmap_1(A_250, '#skF_2', '#skF_4', D_251, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_251)) | ~m1_pre_topc(D_251, '#skF_4') | ~m1_pre_topc(D_251, A_250) | ~m1_pre_topc('#skF_4', A_250) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(negUnitSimplification, [status(thm)], [c_42, c_127])).
% 2.87/1.43  tff(c_135, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_129])).
% 2.87/1.43  tff(c_146, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_30, c_20, c_135])).
% 2.87/1.43  tff(c_147, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_146])).
% 2.87/1.43  tff(c_106, plain, (![A_240, B_241, C_242, D_243]: (k2_partfun1(u1_struct_0(A_240), u1_struct_0(B_241), C_242, u1_struct_0(D_243))=k2_tmap_1(A_240, B_241, C_242, D_243) | ~m1_pre_topc(D_243, A_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), u1_struct_0(B_241)))) | ~v1_funct_2(C_242, u1_struct_0(A_240), u1_struct_0(B_241)) | ~v1_funct_1(C_242) | ~l1_pre_topc(B_241) | ~v2_pre_topc(B_241) | v2_struct_0(B_241) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.43  tff(c_108, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.87/1.43  tff(c_111, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_76, c_40, c_38, c_28, c_26, c_108])).
% 2.87/1.43  tff(c_112, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_42, c_111])).
% 2.87/1.43  tff(c_151, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_147, c_112])).
% 2.87/1.43  tff(c_158, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_151])).
% 2.87/1.43  tff(c_56, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 2.87/1.43  tff(c_57, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 2.87/1.43  tff(c_105, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_102, c_57])).
% 2.87/1.43  tff(c_163, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_105])).
% 2.87/1.43  tff(c_195, plain, (![B_261, F_260, A_259, D_263, C_262]: (r1_tmap_1(B_261, A_259, C_262, F_260) | ~r1_tmap_1(D_263, A_259, k2_tmap_1(B_261, A_259, C_262, D_263), F_260) | ~m1_subset_1(F_260, u1_struct_0(D_263)) | ~m1_subset_1(F_260, u1_struct_0(B_261)) | ~m1_pre_topc(D_263, B_261) | ~v1_tsep_1(D_263, B_261) | v2_struct_0(D_263) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_261), u1_struct_0(A_259)))) | ~v1_funct_2(C_262, u1_struct_0(B_261), u1_struct_0(A_259)) | ~v1_funct_1(C_262) | ~l1_pre_topc(B_261) | ~v2_pre_topc(B_261) | v2_struct_0(B_261) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.87/1.43  tff(c_199, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_163, c_195])).
% 2.87/1.43  tff(c_206, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_95, c_76, c_28, c_26, c_24, c_22, c_20, c_18, c_59, c_199])).
% 2.87/1.43  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_32, c_36, c_102, c_206])).
% 2.87/1.43  tff(c_210, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.87/1.43  tff(c_298, plain, (![D_285, F_282, C_284, B_283, A_281]: (r1_tmap_1(D_285, A_281, k2_tmap_1(B_283, A_281, C_284, D_285), F_282) | ~r1_tmap_1(B_283, A_281, C_284, F_282) | ~m1_subset_1(F_282, u1_struct_0(D_285)) | ~m1_subset_1(F_282, u1_struct_0(B_283)) | ~m1_pre_topc(D_285, B_283) | ~v1_tsep_1(D_285, B_283) | v2_struct_0(D_285) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_283), u1_struct_0(A_281)))) | ~v1_funct_2(C_284, u1_struct_0(B_283), u1_struct_0(A_281)) | ~v1_funct_1(C_284) | ~l1_pre_topc(B_283) | ~v2_pre_topc(B_283) | v2_struct_0(B_283) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.87/1.43  tff(c_300, plain, (![D_285, F_282]: (r1_tmap_1(D_285, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_285), F_282) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_282) | ~m1_subset_1(F_282, u1_struct_0(D_285)) | ~m1_subset_1(F_282, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_285, '#skF_4') | ~v1_tsep_1(D_285, '#skF_4') | v2_struct_0(D_285) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_298])).
% 2.87/1.43  tff(c_303, plain, (![D_285, F_282]: (r1_tmap_1(D_285, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_285), F_282) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_282) | ~m1_subset_1(F_282, u1_struct_0(D_285)) | ~m1_subset_1(F_282, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_285, '#skF_4') | ~v1_tsep_1(D_285, '#skF_4') | v2_struct_0(D_285) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_95, c_76, c_28, c_26, c_300])).
% 2.87/1.43  tff(c_305, plain, (![D_286, F_287]: (r1_tmap_1(D_286, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_286), F_287) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_287) | ~m1_subset_1(F_287, u1_struct_0(D_286)) | ~m1_subset_1(F_287, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_286, '#skF_4') | ~v1_tsep_1(D_286, '#skF_4') | v2_struct_0(D_286))), inference(negUnitSimplification, [status(thm)], [c_42, c_32, c_303])).
% 2.87/1.43  tff(c_231, plain, (![C_273, D_269, E_272, A_270, B_271]: (k3_tmap_1(A_270, B_271, C_273, D_269, E_272)=k2_partfun1(u1_struct_0(C_273), u1_struct_0(B_271), E_272, u1_struct_0(D_269)) | ~m1_pre_topc(D_269, C_273) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_273), u1_struct_0(B_271)))) | ~v1_funct_2(E_272, u1_struct_0(C_273), u1_struct_0(B_271)) | ~v1_funct_1(E_272) | ~m1_pre_topc(D_269, A_270) | ~m1_pre_topc(C_273, A_270) | ~l1_pre_topc(B_271) | ~v2_pre_topc(B_271) | v2_struct_0(B_271) | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.43  tff(c_233, plain, (![A_270, D_269]: (k3_tmap_1(A_270, '#skF_2', '#skF_4', D_269, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_269)) | ~m1_pre_topc(D_269, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_269, A_270) | ~m1_pre_topc('#skF_4', A_270) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(resolution, [status(thm)], [c_24, c_231])).
% 2.87/1.43  tff(c_236, plain, (![A_270, D_269]: (k3_tmap_1(A_270, '#skF_2', '#skF_4', D_269, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_269)) | ~m1_pre_topc(D_269, '#skF_4') | ~m1_pre_topc(D_269, A_270) | ~m1_pre_topc('#skF_4', A_270) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_233])).
% 2.87/1.43  tff(c_238, plain, (![A_274, D_275]: (k3_tmap_1(A_274, '#skF_2', '#skF_4', D_275, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_275)) | ~m1_pre_topc(D_275, '#skF_4') | ~m1_pre_topc(D_275, A_274) | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_42, c_236])).
% 2.87/1.43  tff(c_244, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_238])).
% 2.87/1.43  tff(c_255, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_30, c_20, c_244])).
% 2.87/1.43  tff(c_256, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_255])).
% 2.87/1.43  tff(c_215, plain, (![A_264, B_265, C_266, D_267]: (k2_partfun1(u1_struct_0(A_264), u1_struct_0(B_265), C_266, u1_struct_0(D_267))=k2_tmap_1(A_264, B_265, C_266, D_267) | ~m1_pre_topc(D_267, A_264) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_264), u1_struct_0(B_265)))) | ~v1_funct_2(C_266, u1_struct_0(A_264), u1_struct_0(B_265)) | ~v1_funct_1(C_266) | ~l1_pre_topc(B_265) | ~v2_pre_topc(B_265) | v2_struct_0(B_265) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.43  tff(c_217, plain, (![D_267]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_267))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_267) | ~m1_pre_topc(D_267, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_215])).
% 2.87/1.43  tff(c_220, plain, (![D_267]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_267))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_267) | ~m1_pre_topc(D_267, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_76, c_40, c_38, c_28, c_26, c_217])).
% 2.87/1.43  tff(c_221, plain, (![D_267]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_267))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_267) | ~m1_pre_topc(D_267, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_42, c_220])).
% 2.87/1.43  tff(c_260, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_256, c_221])).
% 2.87/1.43  tff(c_267, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_260])).
% 2.87/1.43  tff(c_209, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.87/1.43  tff(c_272, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_209])).
% 2.87/1.43  tff(c_310, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_305, c_272])).
% 2.87/1.43  tff(c_317, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_59, c_210, c_310])).
% 2.87/1.43  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_317])).
% 2.87/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  Inference rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Ref     : 0
% 2.87/1.43  #Sup     : 48
% 2.87/1.43  #Fact    : 0
% 2.87/1.43  #Define  : 0
% 2.87/1.43  #Split   : 4
% 2.87/1.43  #Chain   : 0
% 2.87/1.43  #Close   : 0
% 2.87/1.43  
% 2.87/1.43  Ordering : KBO
% 2.87/1.43  
% 2.87/1.43  Simplification rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Subsume      : 2
% 2.87/1.43  #Demod        : 115
% 2.87/1.43  #Tautology    : 32
% 2.87/1.43  #SimpNegUnit  : 18
% 2.87/1.43  #BackRed      : 4
% 2.87/1.43  
% 2.87/1.43  #Partial instantiations: 0
% 2.87/1.43  #Strategies tried      : 1
% 2.87/1.43  
% 2.87/1.43  Timing (in seconds)
% 2.87/1.43  ----------------------
% 2.87/1.44  Preprocessing        : 0.37
% 2.87/1.44  Parsing              : 0.18
% 2.87/1.44  CNF conversion       : 0.05
% 2.87/1.44  Main loop            : 0.27
% 2.87/1.44  Inferencing          : 0.10
% 2.87/1.44  Reduction            : 0.09
% 2.87/1.44  Demodulation         : 0.07
% 2.87/1.44  BG Simplification    : 0.02
% 2.87/1.44  Subsumption          : 0.04
% 2.87/1.44  Abstraction          : 0.01
% 2.87/1.44  MUC search           : 0.00
% 2.87/1.44  Cooper               : 0.00
% 2.87/1.44  Total                : 0.70
% 2.87/1.44  Index Insertion      : 0.00
% 2.87/1.44  Index Deletion       : 0.00
% 2.87/1.44  Index Matching       : 0.00
% 2.87/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
