%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 296 expanded)
%              Number of leaves         :   40 ( 129 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (1950 expanded)
%              Number of equality atoms :    6 (  99 expanded)
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

tff(f_246,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_109,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_91,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_203,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_156,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_34,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_82,plain,(
    ! [B_284,A_285] :
      ( l1_pre_topc(B_284)
      | ~ m1_pre_topc(B_284,A_285)
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_42,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_26,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_139,plain,(
    ! [B_305,A_306] :
      ( v3_pre_topc(u1_struct_0(B_305),A_306)
      | ~ v1_tsep_1(B_305,A_306)
      | ~ m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_143,plain,(
    ! [B_33,A_31] :
      ( v3_pre_topc(u1_struct_0(B_33),A_31)
      | ~ v1_tsep_1(B_33,A_31)
      | ~ v2_pre_topc(A_31)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_100,plain,(
    ! [C_292,A_293,B_294] :
      ( m1_subset_1(C_292,u1_struct_0(A_293))
      | ~ m1_subset_1(C_292,u1_struct_0(B_294))
      | ~ m1_pre_topc(B_294,A_293)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_104,plain,(
    ! [A_293] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_293))
      | ~ m1_pre_topc('#skF_4',A_293)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_36,c_100])).

tff(c_110,plain,(
    ! [A_293] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_293))
      | ~ m1_pre_topc('#skF_4',A_293)
      | ~ l1_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_104])).

tff(c_149,plain,(
    ! [B_309,A_310,C_311] :
      ( m1_connsp_2(B_309,A_310,C_311)
      | ~ r2_hidden(C_311,B_309)
      | ~ v3_pre_topc(B_309,A_310)
      | ~ m1_subset_1(C_311,u1_struct_0(A_310))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,(
    ! [B_316,A_317] :
      ( m1_connsp_2(B_316,A_317,'#skF_6')
      | ~ r2_hidden('#skF_6',B_316)
      | ~ v3_pre_topc(B_316,A_317)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ v2_pre_topc(A_317)
      | ~ m1_pre_topc('#skF_4',A_317)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_110,c_149])).

tff(c_187,plain,(
    ! [B_33,A_31] :
      ( m1_connsp_2(u1_struct_0(B_33),A_31,'#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_33))
      | ~ v3_pre_topc(u1_struct_0(B_33),A_31)
      | ~ v2_pre_topc(A_31)
      | ~ m1_pre_topc('#skF_4',A_31)
      | v2_struct_0(A_31)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_98,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_71,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_99,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_71])).

tff(c_197,plain,(
    ! [B_330,G_327,E_329,A_328,C_332,D_331] :
      ( r1_tmap_1(B_330,A_328,C_332,G_327)
      | ~ r1_tmap_1(D_331,A_328,k2_tmap_1(B_330,A_328,C_332,D_331),G_327)
      | ~ m1_connsp_2(E_329,B_330,G_327)
      | ~ r1_tarski(E_329,u1_struct_0(D_331))
      | ~ m1_subset_1(G_327,u1_struct_0(D_331))
      | ~ m1_subset_1(G_327,u1_struct_0(B_330))
      | ~ m1_subset_1(E_329,k1_zfmisc_1(u1_struct_0(B_330)))
      | ~ m1_pre_topc(D_331,B_330)
      | v2_struct_0(D_331)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_330),u1_struct_0(A_328))))
      | ~ v1_funct_2(C_332,u1_struct_0(B_330),u1_struct_0(A_328))
      | ~ v1_funct_1(C_332)
      | ~ l1_pre_topc(B_330)
      | ~ v2_pre_topc(B_330)
      | v2_struct_0(B_330)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_199,plain,(
    ! [E_329] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_329,'#skF_2','#skF_6')
      | ~ r1_tarski(E_329,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_329,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_99,c_197])).

tff(c_202,plain,(
    ! [E_329] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_329,'#skF_2','#skF_6')
      | ~ r1_tarski(E_329,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_329,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_46,c_40,c_72,c_36,c_199])).

tff(c_204,plain,(
    ! [E_333] :
      ( ~ m1_connsp_2(E_333,'#skF_2','#skF_6')
      | ~ r1_tarski(E_333,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_333,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_44,c_98,c_202])).

tff(c_208,plain,(
    ! [B_33] :
      ( ~ m1_connsp_2(u1_struct_0(B_33),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_33),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_33,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_204])).

tff(c_212,plain,(
    ! [B_334] :
      ( ~ m1_connsp_2(u1_struct_0(B_334),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_334),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_334,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_208])).

tff(c_216,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_219,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_216])).

tff(c_222,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_219])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40,c_54,c_222])).

tff(c_232,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_231])).

tff(c_240,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_243,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40,c_54,c_42,c_243])).

tff(c_248,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_258,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_261,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_258])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_264,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_14])).

tff(c_267,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_264])).

tff(c_270,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_267])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_270])).

tff(c_276,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_368,plain,(
    ! [A_364,C_365,D_363,B_366,F_367] :
      ( r1_tmap_1(D_363,A_364,k2_tmap_1(B_366,A_364,C_365,D_363),F_367)
      | ~ r1_tmap_1(B_366,A_364,C_365,F_367)
      | ~ m1_subset_1(F_367,u1_struct_0(D_363))
      | ~ m1_subset_1(F_367,u1_struct_0(B_366))
      | ~ m1_pre_topc(D_363,B_366)
      | v2_struct_0(D_363)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366),u1_struct_0(A_364))))
      | ~ v1_funct_2(C_365,u1_struct_0(B_366),u1_struct_0(A_364))
      | ~ v1_funct_1(C_365)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_370,plain,(
    ! [D_363,F_367] :
      ( r1_tmap_1(D_363,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_363),F_367)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_367)
      | ~ m1_subset_1(F_367,u1_struct_0(D_363))
      | ~ m1_subset_1(F_367,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_363,'#skF_2')
      | v2_struct_0(D_363)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_368])).

tff(c_373,plain,(
    ! [D_363,F_367] :
      ( r1_tmap_1(D_363,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_363),F_367)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_367)
      | ~ m1_subset_1(F_367,u1_struct_0(D_363))
      | ~ m1_subset_1(F_367,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_363,'#skF_2')
      | v2_struct_0(D_363)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_370])).

tff(c_376,plain,(
    ! [D_370,F_371] :
      ( r1_tmap_1(D_370,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_370),F_371)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_371)
      | ~ m1_subset_1(F_371,u1_struct_0(D_370))
      | ~ m1_subset_1(F_371,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_370,'#skF_2')
      | v2_struct_0(D_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_373])).

tff(c_275,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_379,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_376,c_275])).

tff(c_382,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72,c_36,c_276,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:49:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.10/1.48  
% 3.10/1.48  %Foreground sorts:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Background operators:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Foreground operators:
% 3.10/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.10/1.48  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.10/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.10/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.10/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.48  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.10/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.10/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.10/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.10/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.10/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.48  
% 3.20/1.51  tff(f_246, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.20/1.51  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.20/1.51  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.51  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.20/1.51  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.20/1.51  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.20/1.51  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.20/1.51  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.20/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.51  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.20/1.51  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.20/1.51  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.20/1.51  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_34, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_72, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.20/1.51  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_82, plain, (![B_284, A_285]: (l1_pre_topc(B_284) | ~m1_pre_topc(B_284, A_285) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.20/1.51  tff(c_85, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_82])).
% 3.20/1.51  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_85])).
% 3.20/1.51  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.51  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.51  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_42, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_26, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.20/1.51  tff(c_139, plain, (![B_305, A_306]: (v3_pre_topc(u1_struct_0(B_305), A_306) | ~v1_tsep_1(B_305, A_306) | ~m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.20/1.51  tff(c_143, plain, (![B_33, A_31]: (v3_pre_topc(u1_struct_0(B_33), A_31) | ~v1_tsep_1(B_33, A_31) | ~v2_pre_topc(A_31) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_26, c_139])).
% 3.20/1.51  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_100, plain, (![C_292, A_293, B_294]: (m1_subset_1(C_292, u1_struct_0(A_293)) | ~m1_subset_1(C_292, u1_struct_0(B_294)) | ~m1_pre_topc(B_294, A_293) | v2_struct_0(B_294) | ~l1_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.51  tff(c_104, plain, (![A_293]: (m1_subset_1('#skF_6', u1_struct_0(A_293)) | ~m1_pre_topc('#skF_4', A_293) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_36, c_100])).
% 3.20/1.51  tff(c_110, plain, (![A_293]: (m1_subset_1('#skF_6', u1_struct_0(A_293)) | ~m1_pre_topc('#skF_4', A_293) | ~l1_pre_topc(A_293) | v2_struct_0(A_293))), inference(negUnitSimplification, [status(thm)], [c_44, c_104])).
% 3.20/1.51  tff(c_149, plain, (![B_309, A_310, C_311]: (m1_connsp_2(B_309, A_310, C_311) | ~r2_hidden(C_311, B_309) | ~v3_pre_topc(B_309, A_310) | ~m1_subset_1(C_311, u1_struct_0(A_310)) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.20/1.51  tff(c_183, plain, (![B_316, A_317]: (m1_connsp_2(B_316, A_317, '#skF_6') | ~r2_hidden('#skF_6', B_316) | ~v3_pre_topc(B_316, A_317) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_317))) | ~v2_pre_topc(A_317) | ~m1_pre_topc('#skF_4', A_317) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_110, c_149])).
% 3.20/1.51  tff(c_187, plain, (![B_33, A_31]: (m1_connsp_2(u1_struct_0(B_33), A_31, '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_33)) | ~v3_pre_topc(u1_struct_0(B_33), A_31) | ~v2_pre_topc(A_31) | ~m1_pre_topc('#skF_4', A_31) | v2_struct_0(A_31) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_26, c_183])).
% 3.20/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.51  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_64, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_73, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 3.20/1.51  tff(c_98, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_73])).
% 3.20/1.51  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_70, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.20/1.51  tff(c_71, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 3.20/1.51  tff(c_99, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_98, c_71])).
% 3.20/1.51  tff(c_197, plain, (![B_330, G_327, E_329, A_328, C_332, D_331]: (r1_tmap_1(B_330, A_328, C_332, G_327) | ~r1_tmap_1(D_331, A_328, k2_tmap_1(B_330, A_328, C_332, D_331), G_327) | ~m1_connsp_2(E_329, B_330, G_327) | ~r1_tarski(E_329, u1_struct_0(D_331)) | ~m1_subset_1(G_327, u1_struct_0(D_331)) | ~m1_subset_1(G_327, u1_struct_0(B_330)) | ~m1_subset_1(E_329, k1_zfmisc_1(u1_struct_0(B_330))) | ~m1_pre_topc(D_331, B_330) | v2_struct_0(D_331) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_330), u1_struct_0(A_328)))) | ~v1_funct_2(C_332, u1_struct_0(B_330), u1_struct_0(A_328)) | ~v1_funct_1(C_332) | ~l1_pre_topc(B_330) | ~v2_pre_topc(B_330) | v2_struct_0(B_330) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.20/1.51  tff(c_199, plain, (![E_329]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_329, '#skF_2', '#skF_6') | ~r1_tarski(E_329, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_329, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_99, c_197])).
% 3.20/1.51  tff(c_202, plain, (![E_329]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_329, '#skF_2', '#skF_6') | ~r1_tarski(E_329, u1_struct_0('#skF_4')) | ~m1_subset_1(E_329, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_46, c_40, c_72, c_36, c_199])).
% 3.20/1.51  tff(c_204, plain, (![E_333]: (~m1_connsp_2(E_333, '#skF_2', '#skF_6') | ~r1_tarski(E_333, u1_struct_0('#skF_4')) | ~m1_subset_1(E_333, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_44, c_98, c_202])).
% 3.20/1.51  tff(c_208, plain, (![B_33]: (~m1_connsp_2(u1_struct_0(B_33), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_33), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_33, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_204])).
% 3.20/1.51  tff(c_212, plain, (![B_334]: (~m1_connsp_2(u1_struct_0(B_334), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_334), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_334, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_208])).
% 3.20/1.51  tff(c_216, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_212])).
% 3.20/1.51  tff(c_219, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_216])).
% 3.20/1.51  tff(c_222, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_187, c_219])).
% 3.20/1.51  tff(c_231, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_40, c_54, c_222])).
% 3.20/1.51  tff(c_232, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_231])).
% 3.20/1.51  tff(c_240, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_232])).
% 3.20/1.51  tff(c_243, plain, (~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_143, c_240])).
% 3.20/1.51  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_40, c_54, c_42, c_243])).
% 3.20/1.51  tff(c_248, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_232])).
% 3.20/1.51  tff(c_258, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_248])).
% 3.20/1.51  tff(c_261, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_258])).
% 3.20/1.51  tff(c_14, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.20/1.51  tff(c_264, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_261, c_14])).
% 3.20/1.51  tff(c_267, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_264])).
% 3.20/1.51  tff(c_270, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_267])).
% 3.20/1.51  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_270])).
% 3.20/1.51  tff(c_276, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_73])).
% 3.20/1.51  tff(c_368, plain, (![A_364, C_365, D_363, B_366, F_367]: (r1_tmap_1(D_363, A_364, k2_tmap_1(B_366, A_364, C_365, D_363), F_367) | ~r1_tmap_1(B_366, A_364, C_365, F_367) | ~m1_subset_1(F_367, u1_struct_0(D_363)) | ~m1_subset_1(F_367, u1_struct_0(B_366)) | ~m1_pre_topc(D_363, B_366) | v2_struct_0(D_363) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366), u1_struct_0(A_364)))) | ~v1_funct_2(C_365, u1_struct_0(B_366), u1_struct_0(A_364)) | ~v1_funct_1(C_365) | ~l1_pre_topc(B_366) | ~v2_pre_topc(B_366) | v2_struct_0(B_366) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.20/1.51  tff(c_370, plain, (![D_363, F_367]: (r1_tmap_1(D_363, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_363), F_367) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_367) | ~m1_subset_1(F_367, u1_struct_0(D_363)) | ~m1_subset_1(F_367, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_363, '#skF_2') | v2_struct_0(D_363) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_368])).
% 3.20/1.51  tff(c_373, plain, (![D_363, F_367]: (r1_tmap_1(D_363, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_363), F_367) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_367) | ~m1_subset_1(F_367, u1_struct_0(D_363)) | ~m1_subset_1(F_367, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_363, '#skF_2') | v2_struct_0(D_363) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_370])).
% 3.20/1.51  tff(c_376, plain, (![D_370, F_371]: (r1_tmap_1(D_370, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_370), F_371) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_371) | ~m1_subset_1(F_371, u1_struct_0(D_370)) | ~m1_subset_1(F_371, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_370, '#skF_2') | v2_struct_0(D_370))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_373])).
% 3.20/1.51  tff(c_275, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_73])).
% 3.20/1.51  tff(c_379, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_376, c_275])).
% 3.20/1.51  tff(c_382, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_72, c_36, c_276, c_379])).
% 3.20/1.51  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_382])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 0
% 3.20/1.51  #Sup     : 50
% 3.20/1.51  #Fact    : 0
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 4
% 3.20/1.51  #Chain   : 0
% 3.20/1.51  #Close   : 0
% 3.20/1.51  
% 3.20/1.51  Ordering : KBO
% 3.20/1.51  
% 3.20/1.51  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 5
% 3.20/1.51  #Demod        : 72
% 3.20/1.51  #Tautology    : 15
% 3.20/1.51  #SimpNegUnit  : 21
% 3.20/1.51  #BackRed      : 0
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 0
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.51  Preprocessing        : 0.39
% 3.20/1.51  Parsing              : 0.20
% 3.20/1.51  CNF conversion       : 0.05
% 3.20/1.51  Main loop            : 0.30
% 3.20/1.51  Inferencing          : 0.11
% 3.20/1.51  Reduction            : 0.09
% 3.20/1.51  Demodulation         : 0.06
% 3.20/1.51  BG Simplification    : 0.02
% 3.20/1.51  Subsumption          : 0.06
% 3.20/1.51  Abstraction          : 0.01
% 3.20/1.51  MUC search           : 0.00
% 3.20/1.51  Cooper               : 0.00
% 3.20/1.51  Total                : 0.73
% 3.20/1.51  Index Insertion      : 0.00
% 3.20/1.51  Index Deletion       : 0.00
% 3.20/1.51  Index Matching       : 0.00
% 3.20/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
