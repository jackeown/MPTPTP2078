%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 546 expanded)
%              Number of leaves         :   30 ( 210 expanded)
%              Depth                    :   22
%              Number of atoms          :  545 (4287 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_223,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ( m1_pre_topc(D,C)
                         => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                            & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

tff(f_63,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_128,axiom,(
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
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ? [E] :
                        ( m1_subset_1(E,u1_struct_0(C))
                        & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_176,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_36,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_32,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_239,plain,(
    ! [E_305,B_302,D_304,A_306,C_303] :
      ( v1_funct_2(k3_tmap_1(A_306,B_302,C_303,D_304,E_305),u1_struct_0(D_304),u1_struct_0(B_302))
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_303),u1_struct_0(B_302))))
      | ~ v1_funct_2(E_305,u1_struct_0(C_303),u1_struct_0(B_302))
      | ~ v1_funct_1(E_305)
      | ~ m1_pre_topc(D_304,A_306)
      | ~ m1_pre_topc(C_303,A_306)
      | ~ l1_pre_topc(B_302)
      | ~ v2_pre_topc(B_302)
      | v2_struct_0(B_302)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_243,plain,(
    ! [A_306,D_304] :
      ( v1_funct_2(k3_tmap_1(A_306,'#skF_4','#skF_5',D_304,'#skF_7'),u1_struct_0(D_304),u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_304,A_306)
      | ~ m1_pre_topc('#skF_5',A_306)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_250,plain,(
    ! [A_306,D_304] :
      ( v1_funct_2(k3_tmap_1(A_306,'#skF_4','#skF_5',D_304,'#skF_7'),u1_struct_0(D_304),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_304,A_306)
      | ~ m1_pre_topc('#skF_5',A_306)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_243])).

tff(c_252,plain,(
    ! [A_307,D_308] :
      ( v1_funct_2(k3_tmap_1(A_307,'#skF_4','#skF_5',D_308,'#skF_7'),u1_struct_0(D_308),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_308,A_307)
      | ~ m1_pre_topc('#skF_5',A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_250])).

tff(c_186,plain,(
    ! [B_280,C_281,A_284,E_283,D_282] :
      ( m1_subset_1(k3_tmap_1(A_284,B_280,C_281,D_282,E_283),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_282),u1_struct_0(B_280))))
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_281),u1_struct_0(B_280))))
      | ~ v1_funct_2(E_283,u1_struct_0(C_281),u1_struct_0(B_280))
      | ~ v1_funct_1(E_283)
      | ~ m1_pre_topc(D_282,A_284)
      | ~ m1_pre_topc(C_281,A_284)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_113,plain,(
    ! [E_242,A_243,B_239,D_241,C_240] :
      ( v1_funct_1(k3_tmap_1(A_243,B_239,C_240,D_241,E_242))
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(B_239))))
      | ~ v1_funct_2(E_242,u1_struct_0(C_240),u1_struct_0(B_239))
      | ~ v1_funct_1(E_242)
      | ~ m1_pre_topc(D_241,A_243)
      | ~ m1_pre_topc(C_240,A_243)
      | ~ l1_pre_topc(B_239)
      | ~ v2_pre_topc(B_239)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    ! [A_243,D_241] :
      ( v1_funct_1(k3_tmap_1(A_243,'#skF_4','#skF_5',D_241,'#skF_7'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_241,A_243)
      | ~ m1_pre_topc('#skF_5',A_243)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_118,plain,(
    ! [A_243,D_241] :
      ( v1_funct_1(k3_tmap_1(A_243,'#skF_4','#skF_5',D_241,'#skF_7'))
      | ~ m1_pre_topc(D_241,A_243)
      | ~ m1_pre_topc('#skF_5',A_243)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_115])).

tff(c_120,plain,(
    ! [A_244,D_245] :
      ( v1_funct_1(k3_tmap_1(A_244,'#skF_4','#skF_5',D_245,'#skF_7'))
      | ~ m1_pre_topc(D_245,A_244)
      | ~ m1_pre_topc('#skF_5',A_244)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_118])).

tff(c_24,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_74,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_123,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_74])).

tff(c_126,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_123])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_126])).

tff(c_129,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_157,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_195,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_157])).

tff(c_201,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_40,c_36,c_34,c_32,c_28,c_195])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_201])).

tff(c_204,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_206,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_255,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_252,c_206])).

tff(c_258,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_255])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_258])).

tff(c_261,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_26,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_131,plain,(
    ! [B_246,A_247] :
      ( v2_pre_topc(B_246)
      | ~ m1_pre_topc(B_246,A_247)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_131])).

tff(c_149,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_140])).

tff(c_55,plain,(
    ! [B_217,A_218] :
      ( l1_pre_topc(B_217)
      | ~ m1_pre_topc(B_217,A_218)
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_71,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_130,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_262,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_205,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_263,plain,(
    ! [A_309,B_310,C_311] :
      ( m1_subset_1('#skF_2'(A_309,B_310,C_311),u1_struct_0(B_310))
      | v5_pre_topc(C_311,B_310,A_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_310),u1_struct_0(A_309))))
      | ~ v1_funct_2(C_311,u1_struct_0(B_310),u1_struct_0(A_309))
      | ~ v1_funct_1(C_311)
      | ~ l1_pre_topc(B_310)
      | ~ v2_pre_topc(B_310)
      | v2_struct_0(B_310)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_265,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_6'))
    | v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_263])).

tff(c_270,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_6'))
    | v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_149,c_71,c_130,c_262,c_265])).

tff(c_271,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_261,c_270])).

tff(c_12,plain,(
    ! [A_12,B_28,C_36,D_40] :
      ( '#skF_1'(A_12,B_28,C_36,D_40) = D_40
      | ~ m1_subset_1(D_40,u1_struct_0(B_28))
      | ~ m1_pre_topc(B_28,C_36)
      | ~ m1_pre_topc(C_36,A_12)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_28,A_12)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_277,plain,(
    ! [A_12,C_36] :
      ( '#skF_1'(A_12,'#skF_6',C_36,'#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))) = '#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_pre_topc('#skF_6',C_36)
      | ~ m1_pre_topc(C_36,A_12)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc('#skF_6',A_12)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_271,c_12])).

tff(c_281,plain,(
    ! [A_312,C_313] :
      ( '#skF_1'(A_312,'#skF_6',C_313,'#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))) = '#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_pre_topc('#skF_6',C_313)
      | ~ m1_pre_topc(C_313,A_312)
      | v2_struct_0(C_313)
      | ~ m1_pre_topc('#skF_6',A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_277])).

tff(c_14,plain,(
    ! [A_12,B_28,C_36,D_40] :
      ( m1_subset_1('#skF_1'(A_12,B_28,C_36,D_40),u1_struct_0(C_36))
      | ~ m1_subset_1(D_40,u1_struct_0(B_28))
      | ~ m1_pre_topc(B_28,C_36)
      | ~ m1_pre_topc(C_36,A_12)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_28,A_12)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_287,plain,(
    ! [C_313,A_312] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0(C_313))
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',C_313)
      | ~ m1_pre_topc(C_313,A_312)
      | v2_struct_0(C_313)
      | ~ m1_pre_topc('#skF_6',A_312)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312)
      | ~ m1_pre_topc('#skF_6',C_313)
      | ~ m1_pre_topc(C_313,A_312)
      | v2_struct_0(C_313)
      | ~ m1_pre_topc('#skF_6',A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_14])).

tff(c_293,plain,(
    ! [C_313,A_312] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0(C_313))
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_6',C_313)
      | ~ m1_pre_topc(C_313,A_312)
      | v2_struct_0(C_313)
      | ~ m1_pre_topc('#skF_6',A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_287])).

tff(c_296,plain,(
    ! [C_314,A_315] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0(C_314))
      | ~ m1_pre_topc('#skF_6',C_314)
      | ~ m1_pre_topc(C_314,A_315)
      | v2_struct_0(C_314)
      | ~ m1_pre_topc('#skF_6',A_315)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_293])).

tff(c_298,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_296])).

tff(c_305,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_26,c_298])).

tff(c_306,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_305])).

tff(c_30,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_134,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_131])).

tff(c_143,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_67,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_355,plain,(
    ! [B_323,A_324,C_325,D_326] :
      ( r1_tmap_1(B_323,A_324,C_325,D_326)
      | ~ m1_subset_1(D_326,u1_struct_0(B_323))
      | ~ v5_pre_topc(C_325,B_323,A_324)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_323),u1_struct_0(A_324))))
      | ~ v1_funct_2(C_325,u1_struct_0(B_323),u1_struct_0(A_324))
      | ~ v1_funct_1(C_325)
      | ~ l1_pre_topc(B_323)
      | ~ v2_pre_topc(B_323)
      | v2_struct_0(B_323)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_357,plain,(
    ! [A_324,C_325] :
      ( r1_tmap_1('#skF_5',A_324,C_325,'#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ v5_pre_topc(C_325,'#skF_5',A_324)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_324))))
      | ~ v1_funct_2(C_325,u1_struct_0('#skF_5'),u1_struct_0(A_324))
      | ~ v1_funct_1(C_325)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_306,c_355])).

tff(c_364,plain,(
    ! [A_324,C_325] :
      ( r1_tmap_1('#skF_5',A_324,C_325,'#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ v5_pre_topc(C_325,'#skF_5',A_324)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_324))))
      | ~ v1_funct_2(C_325,u1_struct_0('#skF_5'),u1_struct_0(A_324))
      | ~ v1_funct_1(C_325)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_67,c_357])).

tff(c_379,plain,(
    ! [A_329,C_330] :
      ( r1_tmap_1('#skF_5',A_329,C_330,'#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ v5_pre_topc(C_330,'#skF_5',A_329)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_329))))
      | ~ v1_funct_2(C_330,u1_struct_0('#skF_5'),u1_struct_0(A_329))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_364])).

tff(c_382,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_379])).

tff(c_385,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_30,c_382])).

tff(c_386,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_385])).

tff(c_482,plain,(
    ! [G_371,A_372,B_369,D_370,E_373,C_374] :
      ( r1_tmap_1(D_370,B_369,k3_tmap_1(A_372,B_369,C_374,D_370,E_373),G_371)
      | ~ r1_tmap_1(C_374,B_369,E_373,G_371)
      | ~ m1_pre_topc(D_370,C_374)
      | ~ m1_subset_1(G_371,u1_struct_0(D_370))
      | ~ m1_subset_1(G_371,u1_struct_0(C_374))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_374),u1_struct_0(B_369))))
      | ~ v1_funct_2(E_373,u1_struct_0(C_374),u1_struct_0(B_369))
      | ~ v1_funct_1(E_373)
      | ~ m1_pre_topc(D_370,A_372)
      | v2_struct_0(D_370)
      | ~ m1_pre_topc(C_374,A_372)
      | v2_struct_0(C_374)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_488,plain,(
    ! [D_370,A_372,G_371] :
      ( r1_tmap_1(D_370,'#skF_4',k3_tmap_1(A_372,'#skF_4','#skF_5',D_370,'#skF_7'),G_371)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7',G_371)
      | ~ m1_pre_topc(D_370,'#skF_5')
      | ~ m1_subset_1(G_371,u1_struct_0(D_370))
      | ~ m1_subset_1(G_371,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_370,A_372)
      | v2_struct_0(D_370)
      | ~ m1_pre_topc('#skF_5',A_372)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_28,c_482])).

tff(c_496,plain,(
    ! [D_370,A_372,G_371] :
      ( r1_tmap_1(D_370,'#skF_4',k3_tmap_1(A_372,'#skF_4','#skF_5',D_370,'#skF_7'),G_371)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7',G_371)
      | ~ m1_pre_topc(D_370,'#skF_5')
      | ~ m1_subset_1(G_371,u1_struct_0(D_370))
      | ~ m1_subset_1(G_371,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_370,A_372)
      | v2_struct_0(D_370)
      | ~ m1_pre_topc('#skF_5',A_372)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_488])).

tff(c_498,plain,(
    ! [D_375,A_376,G_377] :
      ( r1_tmap_1(D_375,'#skF_4',k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),G_377)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7',G_377)
      | ~ m1_pre_topc(D_375,'#skF_5')
      | ~ m1_subset_1(G_377,u1_struct_0(D_375))
      | ~ m1_subset_1(G_377,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_375,A_376)
      | v2_struct_0(D_375)
      | ~ m1_pre_topc('#skF_5',A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_496])).

tff(c_18,plain,(
    ! [B_54,A_42,C_60] :
      ( ~ r1_tmap_1(B_54,A_42,C_60,'#skF_2'(A_42,B_54,C_60))
      | v5_pre_topc(C_60,B_54,A_42)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_54),u1_struct_0(A_42))))
      | ~ v1_funct_2(C_60,u1_struct_0(B_54),u1_struct_0(A_42))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(B_54)
      | ~ v2_pre_topc(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_501,plain,(
    ! [A_376,D_375] :
      ( v5_pre_topc(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),D_375,'#skF_4')
      | ~ m1_subset_1(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_375),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),u1_struct_0(D_375),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'))
      | ~ l1_pre_topc(D_375)
      | ~ v2_pre_topc(D_375)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')))
      | ~ m1_pre_topc(D_375,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')),u1_struct_0(D_375))
      | ~ m1_subset_1('#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_375,A_376)
      | v2_struct_0(D_375)
      | ~ m1_pre_topc('#skF_5',A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_498,c_18])).

tff(c_504,plain,(
    ! [A_376,D_375] :
      ( v5_pre_topc(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),D_375,'#skF_4')
      | ~ m1_subset_1(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_375),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'),u1_struct_0(D_375),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7'))
      | ~ l1_pre_topc(D_375)
      | ~ v2_pre_topc(D_375)
      | v2_struct_0('#skF_4')
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')))
      | ~ m1_pre_topc(D_375,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')),u1_struct_0(D_375))
      | ~ m1_subset_1('#skF_2'('#skF_4',D_375,k3_tmap_1(A_376,'#skF_4','#skF_5',D_375,'#skF_7')),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_375,A_376)
      | v2_struct_0(D_375)
      | ~ m1_pre_topc('#skF_5',A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_501])).

tff(c_2049,plain,(
    ! [A_510,D_511] :
      ( v5_pre_topc(k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7'),D_511,'#skF_4')
      | ~ m1_subset_1(k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_511),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7'),u1_struct_0(D_511),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7'))
      | ~ l1_pre_topc(D_511)
      | ~ v2_pre_topc(D_511)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4',D_511,k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7')))
      | ~ m1_pre_topc(D_511,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_4',D_511,k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7')),u1_struct_0(D_511))
      | ~ m1_subset_1('#skF_2'('#skF_4',D_511,k3_tmap_1(A_510,'#skF_4','#skF_5',D_511,'#skF_7')),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_511,A_510)
      | v2_struct_0(D_511)
      | ~ m1_pre_topc('#skF_5',A_510)
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_504])).

tff(c_2054,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_7','#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_205,c_2049])).

tff(c_2061,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_306,c_271,c_26,c_386,c_149,c_71,c_130,c_262,c_2054])).

tff(c_2063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_38,c_261,c_2061])).

%------------------------------------------------------------------------------
