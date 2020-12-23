%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1776+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 210 expanded)
%              Number of leaves         :   28 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  314 (1819 expanded)
%              Number of equality atoms :    3 (  78 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_24,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_153,plain,(
    ! [B_292,C_293,A_294] :
      ( r1_tarski(u1_struct_0(B_292),u1_struct_0(C_293))
      | ~ m1_pre_topc(B_292,C_293)
      | ~ m1_pre_topc(C_293,A_294)
      | ~ m1_pre_topc(B_292,A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_155,plain,(
    ! [B_292] :
      ( r1_tarski(u1_struct_0(B_292),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_292,'#skF_4')
      | ~ m1_pre_topc(B_292,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_162,plain,(
    ! [B_292] :
      ( r1_tarski(u1_struct_0(B_292),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_292,'#skF_4')
      | ~ m1_pre_topc(B_292,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_155])).

tff(c_175,plain,(
    ! [B_297,C_298,A_299] :
      ( v1_tsep_1(B_297,C_298)
      | ~ r1_tarski(u1_struct_0(B_297),u1_struct_0(C_298))
      | ~ m1_pre_topc(C_298,A_299)
      | v2_struct_0(C_298)
      | ~ m1_pre_topc(B_297,A_299)
      | ~ v1_tsep_1(B_297,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,(
    ! [B_292,A_299] :
      ( v1_tsep_1(B_292,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_299)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_292,A_299)
      | ~ v1_tsep_1(B_292,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299)
      | ~ m1_pre_topc(B_292,'#skF_4')
      | ~ m1_pre_topc(B_292,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_162,c_175])).

tff(c_195,plain,(
    ! [B_302,A_303] :
      ( v1_tsep_1(B_302,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_303)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ v1_tsep_1(B_302,A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303)
      | ~ m1_pre_topc(B_302,'#skF_4')
      | ~ m1_pre_topc(B_302,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_179])).

tff(c_197,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_195])).

tff(c_200,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20,c_42,c_40,c_32,c_197])).

tff(c_201,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_200])).

tff(c_18,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_16,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_52,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_61,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_67,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    ! [B_265,C_266,A_267] :
      ( r1_tarski(u1_struct_0(B_265),u1_struct_0(C_266))
      | ~ m1_pre_topc(B_265,C_266)
      | ~ m1_pre_topc(C_266,A_267)
      | ~ m1_pre_topc(B_265,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [B_265] :
      ( r1_tarski(u1_struct_0(B_265),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_265,'#skF_4')
      | ~ m1_pre_topc(B_265,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_79,plain,(
    ! [B_265] :
      ( r1_tarski(u1_struct_0(B_265),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_265,'#skF_4')
      | ~ m1_pre_topc(B_265,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72])).

tff(c_88,plain,(
    ! [B_269,C_270,A_271] :
      ( v1_tsep_1(B_269,C_270)
      | ~ r1_tarski(u1_struct_0(B_269),u1_struct_0(C_270))
      | ~ m1_pre_topc(C_270,A_271)
      | v2_struct_0(C_270)
      | ~ m1_pre_topc(B_269,A_271)
      | ~ v1_tsep_1(B_269,A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [B_265,A_271] :
      ( v1_tsep_1(B_265,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_271)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_265,A_271)
      | ~ v1_tsep_1(B_265,A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271)
      | ~ m1_pre_topc(B_265,'#skF_4')
      | ~ m1_pre_topc(B_265,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_79,c_88])).

tff(c_104,plain,(
    ! [B_273,A_274] :
      ( v1_tsep_1(B_273,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc(B_273,A_274)
      | ~ v1_tsep_1(B_273,A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_273,'#skF_4')
      | ~ m1_pre_topc(B_273,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_90])).

tff(c_106,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_109,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20,c_42,c_40,c_32,c_106])).

tff(c_110,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_109])).

tff(c_58,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_68,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_138,plain,(
    ! [E_285,G_284,D_283,A_287,C_286,B_288] :
      ( r1_tmap_1(D_283,B_288,E_285,G_284)
      | ~ r1_tmap_1(C_286,B_288,k3_tmap_1(A_287,B_288,D_283,C_286,E_285),G_284)
      | ~ m1_subset_1(G_284,u1_struct_0(C_286))
      | ~ m1_subset_1(G_284,u1_struct_0(D_283))
      | ~ m1_pre_topc(C_286,D_283)
      | ~ v1_tsep_1(C_286,D_283)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_283),u1_struct_0(B_288))))
      | ~ v1_funct_2(E_285,u1_struct_0(D_283),u1_struct_0(B_288))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc(D_283,A_287)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(C_286,A_287)
      | v2_struct_0(C_286)
      | ~ l1_pre_topc(B_288)
      | ~ v2_pre_topc(B_288)
      | v2_struct_0(B_288)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_140,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_138])).

tff(c_143,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_48,c_46,c_36,c_32,c_30,c_28,c_26,c_110,c_20,c_18,c_62,c_140])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_38,c_34,c_67,c_143])).

tff(c_146,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_146])).

tff(c_150,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_214,plain,(
    ! [A_308,G_305,E_306,C_307,D_304,B_309] :
      ( r1_tmap_1(C_307,B_309,k3_tmap_1(A_308,B_309,D_304,C_307,E_306),G_305)
      | ~ r1_tmap_1(D_304,B_309,E_306,G_305)
      | ~ m1_subset_1(G_305,u1_struct_0(C_307))
      | ~ m1_subset_1(G_305,u1_struct_0(D_304))
      | ~ m1_pre_topc(C_307,D_304)
      | ~ v1_tsep_1(C_307,D_304)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_304),u1_struct_0(B_309))))
      | ~ v1_funct_2(E_306,u1_struct_0(D_304),u1_struct_0(B_309))
      | ~ v1_funct_1(E_306)
      | ~ m1_pre_topc(D_304,A_308)
      | v2_struct_0(D_304)
      | ~ m1_pre_topc(C_307,A_308)
      | v2_struct_0(C_307)
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_216,plain,(
    ! [C_307,A_308,G_305] :
      ( r1_tmap_1(C_307,'#skF_1',k3_tmap_1(A_308,'#skF_1','#skF_4',C_307,'#skF_5'),G_305)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_305)
      | ~ m1_subset_1(G_305,u1_struct_0(C_307))
      | ~ m1_subset_1(G_305,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(C_307,'#skF_4')
      | ~ v1_tsep_1(C_307,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_308)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_307,A_308)
      | v2_struct_0(C_307)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_26,c_214])).

tff(c_219,plain,(
    ! [C_307,A_308,G_305] :
      ( r1_tmap_1(C_307,'#skF_1',k3_tmap_1(A_308,'#skF_1','#skF_4',C_307,'#skF_5'),G_305)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_305)
      | ~ m1_subset_1(G_305,u1_struct_0(C_307))
      | ~ m1_subset_1(G_305,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(C_307,'#skF_4')
      | ~ v1_tsep_1(C_307,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_308)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_307,A_308)
      | v2_struct_0(C_307)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_28,c_216])).

tff(c_221,plain,(
    ! [C_310,A_311,G_312] :
      ( r1_tmap_1(C_310,'#skF_1',k3_tmap_1(A_311,'#skF_1','#skF_4',C_310,'#skF_5'),G_312)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_312)
      | ~ m1_subset_1(G_312,u1_struct_0(C_310))
      | ~ m1_subset_1(G_312,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(C_310,'#skF_4')
      | ~ v1_tsep_1(C_310,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_311)
      | ~ m1_pre_topc(C_310,A_311)
      | v2_struct_0(C_310)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34,c_219])).

tff(c_149,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_224,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_221,c_149])).

tff(c_227,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_32,c_201,c_20,c_18,c_62,c_150,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_227])).

%------------------------------------------------------------------------------
