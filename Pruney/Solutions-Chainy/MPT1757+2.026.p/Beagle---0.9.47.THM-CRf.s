%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 252 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  360 (1518 expanded)
%              Number of equality atoms :    5 (  73 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_278,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_105,axiom,(
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

tff(f_148,axiom,(
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

tff(f_235,axiom,(
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

tff(f_188,axiom,(
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
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_38,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_85,plain,(
    ! [B_297,A_298] :
      ( l1_pre_topc(B_297)
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_95,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_91])).

tff(c_26,plain,(
    ! [A_39] :
      ( m1_pre_topc(A_39,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_305,A_306] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_307,A_308,B_309] :
      ( m1_subset_1(A_307,u1_struct_0(A_308))
      | ~ r2_hidden(A_307,u1_struct_0(B_309))
      | ~ m1_pre_topc(B_309,A_308)
      | ~ l1_pre_topc(A_308) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_114,plain,(
    ! [A_310,A_311,B_312] :
      ( m1_subset_1(A_310,u1_struct_0(A_311))
      | ~ m1_pre_topc(B_312,A_311)
      | ~ l1_pre_topc(A_311)
      | v1_xboole_0(u1_struct_0(B_312))
      | ~ m1_subset_1(A_310,u1_struct_0(B_312)) ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_118,plain,(
    ! [A_310] :
      ( m1_subset_1(A_310,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_310,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_114])).

tff(c_122,plain,(
    ! [A_310] :
      ( m1_subset_1(A_310,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_310,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_118])).

tff(c_123,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_129,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_126])).

tff(c_132,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_132])).

tff(c_138,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_46,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_24,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_227,plain,(
    ! [B_341,A_342] :
      ( v3_pre_topc(u1_struct_0(B_341),A_342)
      | ~ v1_tsep_1(B_341,A_342)
      | ~ m1_subset_1(u1_struct_0(B_341),k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_pre_topc(B_341,A_342)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_231,plain,(
    ! [B_38,A_36] :
      ( v3_pre_topc(u1_struct_0(B_38),A_36)
      | ~ v1_tsep_1(B_38,A_36)
      | ~ v2_pre_topc(A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_227])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_237,plain,(
    ! [B_345,A_346,C_347] :
      ( m1_connsp_2(B_345,A_346,C_347)
      | ~ r2_hidden(C_347,B_345)
      | ~ v3_pre_topc(B_345,A_346)
      | ~ m1_subset_1(C_347,u1_struct_0(A_346))
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_245,plain,(
    ! [B_345] :
      ( m1_connsp_2(B_345,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_345)
      | ~ v3_pre_topc(B_345,'#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_76,c_237])).

tff(c_256,plain,(
    ! [B_345] :
      ( m1_connsp_2(B_345,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_345)
      | ~ v3_pre_topc(B_345,'#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_245])).

tff(c_262,plain,(
    ! [B_348] :
      ( m1_connsp_2(B_348,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_348)
      | ~ v3_pre_topc(B_348,'#skF_2')
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_256])).

tff(c_266,plain,(
    ! [B_38] :
      ( m1_connsp_2(u1_struct_0(B_38),'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_38))
      | ~ v3_pre_topc(u1_struct_0(B_38),'#skF_2')
      | ~ m1_pre_topc(B_38,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_262])).

tff(c_269,plain,(
    ! [B_38] :
      ( m1_connsp_2(u1_struct_0(B_38),'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_38))
      | ~ v3_pre_topc(u1_struct_0(B_38),'#skF_2')
      | ~ m1_pre_topc(B_38,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_266])).

tff(c_193,plain,(
    ! [B_326,C_327,A_328] :
      ( r1_tarski(u1_struct_0(B_326),u1_struct_0(C_327))
      | ~ m1_pre_topc(B_326,C_327)
      | ~ m1_pre_topc(C_327,A_328)
      | ~ m1_pre_topc(B_326,A_328)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_197,plain,(
    ! [B_326] :
      ( r1_tarski(u1_struct_0(B_326),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_326,'#skF_4')
      | ~ m1_pre_topc(B_326,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_193])).

tff(c_201,plain,(
    ! [B_326] :
      ( r1_tarski(u1_struct_0(B_326),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_326,'#skF_4')
      | ~ m1_pre_topc(B_326,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_197])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_111,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_77,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68])).

tff(c_113,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_77])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_381,plain,(
    ! [G_378,C_375,B_379,A_374,D_377,E_376] :
      ( r1_tmap_1(B_379,A_374,C_375,G_378)
      | ~ r1_tmap_1(D_377,A_374,k2_tmap_1(B_379,A_374,C_375,D_377),G_378)
      | ~ m1_connsp_2(E_376,B_379,G_378)
      | ~ r1_tarski(E_376,u1_struct_0(D_377))
      | ~ m1_subset_1(G_378,u1_struct_0(D_377))
      | ~ m1_subset_1(G_378,u1_struct_0(B_379))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(u1_struct_0(B_379)))
      | ~ m1_pre_topc(D_377,B_379)
      | v2_struct_0(D_377)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_379),u1_struct_0(A_374))))
      | ~ v1_funct_2(C_375,u1_struct_0(B_379),u1_struct_0(A_374))
      | ~ v1_funct_1(C_375)
      | ~ l1_pre_topc(B_379)
      | ~ v2_pre_topc(B_379)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_383,plain,(
    ! [E_376] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_376,'#skF_2','#skF_6')
      | ~ r1_tarski(E_376,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_111,c_381])).

tff(c_386,plain,(
    ! [E_376] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_376,'#skF_2','#skF_6')
      | ~ r1_tarski(E_376,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_44,c_76,c_40,c_383])).

tff(c_388,plain,(
    ! [E_380] :
      ( ~ m1_connsp_2(E_380,'#skF_2','#skF_6')
      | ~ r1_tarski(E_380,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_380,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_48,c_113,c_386])).

tff(c_395,plain,(
    ! [B_38] :
      ( ~ m1_connsp_2(u1_struct_0(B_38),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_38),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_38,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_388])).

tff(c_400,plain,(
    ! [B_381] :
      ( ~ m1_connsp_2(u1_struct_0(B_381),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_381),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_381,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_395])).

tff(c_412,plain,(
    ! [B_382] :
      ( ~ m1_connsp_2(u1_struct_0(B_382),'#skF_2','#skF_6')
      | ~ m1_pre_topc(B_382,'#skF_4')
      | ~ m1_pre_topc(B_382,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_201,c_400])).

tff(c_431,plain,(
    ! [B_385] :
      ( ~ m1_pre_topc(B_385,'#skF_4')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_385))
      | ~ v3_pre_topc(u1_struct_0(B_385),'#skF_2')
      | ~ m1_pre_topc(B_385,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_269,c_412])).

tff(c_435,plain,(
    ! [B_38] :
      ( ~ m1_pre_topc(B_38,'#skF_4')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_38))
      | ~ v1_tsep_1(B_38,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_38,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_231,c_431])).

tff(c_439,plain,(
    ! [B_386] :
      ( ~ m1_pre_topc(B_386,'#skF_4')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_386))
      | ~ v1_tsep_1(B_386,'#skF_2')
      | ~ m1_pre_topc(B_386,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_435])).

tff(c_444,plain,(
    ! [B_387] :
      ( ~ m1_pre_topc(B_387,'#skF_4')
      | ~ v1_tsep_1(B_387,'#skF_2')
      | ~ m1_pre_topc(B_387,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_387))
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_387)) ) ),
    inference(resolution,[status(thm)],[c_2,c_439])).

tff(c_460,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_444])).

tff(c_469,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_460])).

tff(c_470,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_469])).

tff(c_473,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_470])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_473])).

tff(c_478,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_654,plain,(
    ! [C_432,F_431,A_429,B_433,D_430] :
      ( r1_tmap_1(D_430,A_429,k2_tmap_1(B_433,A_429,C_432,D_430),F_431)
      | ~ r1_tmap_1(B_433,A_429,C_432,F_431)
      | ~ m1_subset_1(F_431,u1_struct_0(D_430))
      | ~ m1_subset_1(F_431,u1_struct_0(B_433))
      | ~ m1_pre_topc(D_430,B_433)
      | v2_struct_0(D_430)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433),u1_struct_0(A_429))))
      | ~ v1_funct_2(C_432,u1_struct_0(B_433),u1_struct_0(A_429))
      | ~ v1_funct_1(C_432)
      | ~ l1_pre_topc(B_433)
      | ~ v2_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_656,plain,(
    ! [D_430,F_431] :
      ( r1_tmap_1(D_430,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_430),F_431)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_431)
      | ~ m1_subset_1(F_431,u1_struct_0(D_430))
      | ~ m1_subset_1(F_431,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_430,'#skF_2')
      | v2_struct_0(D_430)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_654])).

tff(c_659,plain,(
    ! [D_430,F_431] :
      ( r1_tmap_1(D_430,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_430),F_431)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_431)
      | ~ m1_subset_1(F_431,u1_struct_0(D_430))
      | ~ m1_subset_1(F_431,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_430,'#skF_2')
      | v2_struct_0(D_430)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_656])).

tff(c_758,plain,(
    ! [D_462,F_463] :
      ( r1_tmap_1(D_462,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_462),F_463)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_463)
      | ~ m1_subset_1(F_463,u1_struct_0(D_462))
      | ~ m1_subset_1(F_463,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_462,'#skF_2')
      | v2_struct_0(D_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_659])).

tff(c_479,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_763,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_758,c_479])).

tff(c_770,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_40,c_478,c_763])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.57  
% 3.56/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.57  
% 3.56/1.57  %Foreground sorts:
% 3.56/1.57  
% 3.56/1.57  
% 3.56/1.57  %Background operators:
% 3.56/1.57  
% 3.56/1.57  
% 3.56/1.57  %Foreground operators:
% 3.56/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.56/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.56/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.56/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.56/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.56/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.57  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.56/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.56/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.56/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.57  
% 3.86/1.59  tff(f_278, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.86/1.59  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.86/1.59  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.86/1.59  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.59  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.86/1.59  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.86/1.59  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.86/1.59  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.86/1.59  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.86/1.59  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.86/1.59  tff(f_148, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.86/1.59  tff(f_235, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.86/1.59  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.86/1.59  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_38, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_76, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 3.86/1.59  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_85, plain, (![B_297, A_298]: (l1_pre_topc(B_297) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.86/1.59  tff(c_91, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_85])).
% 3.86/1.59  tff(c_95, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_91])).
% 3.86/1.59  tff(c_26, plain, (![A_39]: (m1_pre_topc(A_39, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.59  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.86/1.59  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.59  tff(c_102, plain, (![B_305, A_306]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.86/1.59  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.86/1.59  tff(c_106, plain, (![A_307, A_308, B_309]: (m1_subset_1(A_307, u1_struct_0(A_308)) | ~r2_hidden(A_307, u1_struct_0(B_309)) | ~m1_pre_topc(B_309, A_308) | ~l1_pre_topc(A_308))), inference(resolution, [status(thm)], [c_102, c_4])).
% 3.86/1.59  tff(c_114, plain, (![A_310, A_311, B_312]: (m1_subset_1(A_310, u1_struct_0(A_311)) | ~m1_pre_topc(B_312, A_311) | ~l1_pre_topc(A_311) | v1_xboole_0(u1_struct_0(B_312)) | ~m1_subset_1(A_310, u1_struct_0(B_312)))), inference(resolution, [status(thm)], [c_2, c_106])).
% 3.86/1.59  tff(c_118, plain, (![A_310]: (m1_subset_1(A_310, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_310, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_114])).
% 3.86/1.59  tff(c_122, plain, (![A_310]: (m1_subset_1(A_310, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_310, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_118])).
% 3.86/1.59  tff(c_123, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_122])).
% 3.86/1.59  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.86/1.59  tff(c_126, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_123, c_10])).
% 3.86/1.59  tff(c_129, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_126])).
% 3.86/1.59  tff(c_132, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_129])).
% 3.86/1.59  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_132])).
% 3.86/1.59  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_122])).
% 3.86/1.59  tff(c_46, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_24, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.86/1.59  tff(c_227, plain, (![B_341, A_342]: (v3_pre_topc(u1_struct_0(B_341), A_342) | ~v1_tsep_1(B_341, A_342) | ~m1_subset_1(u1_struct_0(B_341), k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_pre_topc(B_341, A_342) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.59  tff(c_231, plain, (![B_38, A_36]: (v3_pre_topc(u1_struct_0(B_38), A_36) | ~v1_tsep_1(B_38, A_36) | ~v2_pre_topc(A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_24, c_227])).
% 3.86/1.59  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_237, plain, (![B_345, A_346, C_347]: (m1_connsp_2(B_345, A_346, C_347) | ~r2_hidden(C_347, B_345) | ~v3_pre_topc(B_345, A_346) | ~m1_subset_1(C_347, u1_struct_0(A_346)) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.86/1.59  tff(c_245, plain, (![B_345]: (m1_connsp_2(B_345, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_345) | ~v3_pre_topc(B_345, '#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_237])).
% 3.86/1.59  tff(c_256, plain, (![B_345]: (m1_connsp_2(B_345, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_345) | ~v3_pre_topc(B_345, '#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_245])).
% 3.86/1.59  tff(c_262, plain, (![B_348]: (m1_connsp_2(B_348, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_348) | ~v3_pre_topc(B_348, '#skF_2') | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_256])).
% 3.86/1.59  tff(c_266, plain, (![B_38]: (m1_connsp_2(u1_struct_0(B_38), '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_38)) | ~v3_pre_topc(u1_struct_0(B_38), '#skF_2') | ~m1_pre_topc(B_38, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_262])).
% 3.86/1.59  tff(c_269, plain, (![B_38]: (m1_connsp_2(u1_struct_0(B_38), '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_38)) | ~v3_pre_topc(u1_struct_0(B_38), '#skF_2') | ~m1_pre_topc(B_38, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_266])).
% 3.86/1.59  tff(c_193, plain, (![B_326, C_327, A_328]: (r1_tarski(u1_struct_0(B_326), u1_struct_0(C_327)) | ~m1_pre_topc(B_326, C_327) | ~m1_pre_topc(C_327, A_328) | ~m1_pre_topc(B_326, A_328) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.86/1.59  tff(c_197, plain, (![B_326]: (r1_tarski(u1_struct_0(B_326), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_326, '#skF_4') | ~m1_pre_topc(B_326, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_193])).
% 3.86/1.59  tff(c_201, plain, (![B_326]: (r1_tarski(u1_struct_0(B_326), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_326, '#skF_4') | ~m1_pre_topc(B_326, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_197])).
% 3.86/1.59  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_74, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_75, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74])).
% 3.86/1.59  tff(c_111, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_75])).
% 3.86/1.59  tff(c_68, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_77, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68])).
% 3.86/1.59  tff(c_113, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_77])).
% 3.86/1.59  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.86/1.59  tff(c_381, plain, (![G_378, C_375, B_379, A_374, D_377, E_376]: (r1_tmap_1(B_379, A_374, C_375, G_378) | ~r1_tmap_1(D_377, A_374, k2_tmap_1(B_379, A_374, C_375, D_377), G_378) | ~m1_connsp_2(E_376, B_379, G_378) | ~r1_tarski(E_376, u1_struct_0(D_377)) | ~m1_subset_1(G_378, u1_struct_0(D_377)) | ~m1_subset_1(G_378, u1_struct_0(B_379)) | ~m1_subset_1(E_376, k1_zfmisc_1(u1_struct_0(B_379))) | ~m1_pre_topc(D_377, B_379) | v2_struct_0(D_377) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_379), u1_struct_0(A_374)))) | ~v1_funct_2(C_375, u1_struct_0(B_379), u1_struct_0(A_374)) | ~v1_funct_1(C_375) | ~l1_pre_topc(B_379) | ~v2_pre_topc(B_379) | v2_struct_0(B_379) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_235])).
% 3.86/1.59  tff(c_383, plain, (![E_376]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_376, '#skF_2', '#skF_6') | ~r1_tarski(E_376, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_376, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_381])).
% 3.86/1.59  tff(c_386, plain, (![E_376]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_376, '#skF_2', '#skF_6') | ~r1_tarski(E_376, u1_struct_0('#skF_4')) | ~m1_subset_1(E_376, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_50, c_44, c_76, c_40, c_383])).
% 3.86/1.59  tff(c_388, plain, (![E_380]: (~m1_connsp_2(E_380, '#skF_2', '#skF_6') | ~r1_tarski(E_380, u1_struct_0('#skF_4')) | ~m1_subset_1(E_380, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_48, c_113, c_386])).
% 3.86/1.59  tff(c_395, plain, (![B_38]: (~m1_connsp_2(u1_struct_0(B_38), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_38), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_38, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_388])).
% 3.86/1.59  tff(c_400, plain, (![B_381]: (~m1_connsp_2(u1_struct_0(B_381), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_381), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_381, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_395])).
% 3.86/1.59  tff(c_412, plain, (![B_382]: (~m1_connsp_2(u1_struct_0(B_382), '#skF_2', '#skF_6') | ~m1_pre_topc(B_382, '#skF_4') | ~m1_pre_topc(B_382, '#skF_2'))), inference(resolution, [status(thm)], [c_201, c_400])).
% 3.86/1.59  tff(c_431, plain, (![B_385]: (~m1_pre_topc(B_385, '#skF_4') | ~r2_hidden('#skF_6', u1_struct_0(B_385)) | ~v3_pre_topc(u1_struct_0(B_385), '#skF_2') | ~m1_pre_topc(B_385, '#skF_2'))), inference(resolution, [status(thm)], [c_269, c_412])).
% 3.86/1.59  tff(c_435, plain, (![B_38]: (~m1_pre_topc(B_38, '#skF_4') | ~r2_hidden('#skF_6', u1_struct_0(B_38)) | ~v1_tsep_1(B_38, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_38, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_231, c_431])).
% 3.86/1.59  tff(c_439, plain, (![B_386]: (~m1_pre_topc(B_386, '#skF_4') | ~r2_hidden('#skF_6', u1_struct_0(B_386)) | ~v1_tsep_1(B_386, '#skF_2') | ~m1_pre_topc(B_386, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_435])).
% 3.86/1.59  tff(c_444, plain, (![B_387]: (~m1_pre_topc(B_387, '#skF_4') | ~v1_tsep_1(B_387, '#skF_2') | ~m1_pre_topc(B_387, '#skF_2') | v1_xboole_0(u1_struct_0(B_387)) | ~m1_subset_1('#skF_6', u1_struct_0(B_387)))), inference(resolution, [status(thm)], [c_2, c_439])).
% 3.86/1.59  tff(c_460, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_444])).
% 3.86/1.59  tff(c_469, plain, (~m1_pre_topc('#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_460])).
% 3.86/1.59  tff(c_470, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_138, c_469])).
% 3.86/1.59  tff(c_473, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_470])).
% 3.86/1.59  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_473])).
% 3.86/1.59  tff(c_478, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.86/1.59  tff(c_654, plain, (![C_432, F_431, A_429, B_433, D_430]: (r1_tmap_1(D_430, A_429, k2_tmap_1(B_433, A_429, C_432, D_430), F_431) | ~r1_tmap_1(B_433, A_429, C_432, F_431) | ~m1_subset_1(F_431, u1_struct_0(D_430)) | ~m1_subset_1(F_431, u1_struct_0(B_433)) | ~m1_pre_topc(D_430, B_433) | v2_struct_0(D_430) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433), u1_struct_0(A_429)))) | ~v1_funct_2(C_432, u1_struct_0(B_433), u1_struct_0(A_429)) | ~v1_funct_1(C_432) | ~l1_pre_topc(B_433) | ~v2_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.59  tff(c_656, plain, (![D_430, F_431]: (r1_tmap_1(D_430, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_430), F_431) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_431) | ~m1_subset_1(F_431, u1_struct_0(D_430)) | ~m1_subset_1(F_431, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_430, '#skF_2') | v2_struct_0(D_430) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_654])).
% 3.86/1.59  tff(c_659, plain, (![D_430, F_431]: (r1_tmap_1(D_430, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_430), F_431) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_431) | ~m1_subset_1(F_431, u1_struct_0(D_430)) | ~m1_subset_1(F_431, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_430, '#skF_2') | v2_struct_0(D_430) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_656])).
% 3.86/1.59  tff(c_758, plain, (![D_462, F_463]: (r1_tmap_1(D_462, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_462), F_463) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_463) | ~m1_subset_1(F_463, u1_struct_0(D_462)) | ~m1_subset_1(F_463, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_462, '#skF_2') | v2_struct_0(D_462))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_659])).
% 3.86/1.59  tff(c_479, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.86/1.59  tff(c_763, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_758, c_479])).
% 3.86/1.59  tff(c_770, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_40, c_478, c_763])).
% 3.86/1.59  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_770])).
% 3.86/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.59  
% 3.86/1.59  Inference rules
% 3.86/1.59  ----------------------
% 3.86/1.59  #Ref     : 0
% 3.86/1.59  #Sup     : 125
% 3.86/1.59  #Fact    : 0
% 3.86/1.59  #Define  : 0
% 3.86/1.59  #Split   : 5
% 3.86/1.59  #Chain   : 0
% 3.86/1.59  #Close   : 0
% 3.86/1.59  
% 3.86/1.59  Ordering : KBO
% 3.86/1.59  
% 3.86/1.59  Simplification rules
% 3.86/1.59  ----------------------
% 3.86/1.59  #Subsume      : 29
% 3.86/1.59  #Demod        : 135
% 3.86/1.59  #Tautology    : 28
% 3.86/1.59  #SimpNegUnit  : 39
% 3.86/1.59  #BackRed      : 0
% 3.86/1.59  
% 3.86/1.59  #Partial instantiations: 0
% 3.86/1.59  #Strategies tried      : 1
% 3.86/1.59  
% 3.86/1.59  Timing (in seconds)
% 3.86/1.59  ----------------------
% 3.86/1.60  Preprocessing        : 0.40
% 3.86/1.60  Parsing              : 0.21
% 3.86/1.60  CNF conversion       : 0.05
% 3.86/1.60  Main loop            : 0.42
% 3.86/1.60  Inferencing          : 0.16
% 3.86/1.60  Reduction            : 0.12
% 3.86/1.60  Demodulation         : 0.09
% 3.86/1.60  BG Simplification    : 0.03
% 3.86/1.60  Subsumption          : 0.09
% 3.86/1.60  Abstraction          : 0.02
% 3.86/1.60  MUC search           : 0.00
% 3.86/1.60  Cooper               : 0.00
% 3.86/1.60  Total                : 0.87
% 3.86/1.60  Index Insertion      : 0.00
% 3.86/1.60  Index Deletion       : 0.00
% 3.86/1.60  Index Matching       : 0.00
% 3.86/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
