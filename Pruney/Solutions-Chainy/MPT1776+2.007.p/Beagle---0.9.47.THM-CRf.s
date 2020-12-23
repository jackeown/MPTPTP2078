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
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 377 expanded)
%              Number of leaves         :   35 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  478 (3095 expanded)
%              Number of equality atoms :   31 ( 153 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_242,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_104,axiom,(
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

tff(f_72,axiom,(
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

tff(f_177,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_36,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_79,plain,(
    ! [B_255,A_256] :
      ( l1_pre_topc(B_255)
      | ~ m1_pre_topc(B_255,A_256)
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_92,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_357,plain,(
    ! [B_310,A_311] :
      ( m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_361,plain,(
    ! [B_310,A_311] :
      ( r1_tarski(u1_struct_0(B_310),u1_struct_0(A_311))
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(resolution,[status(thm)],[c_357,c_2])).

tff(c_414,plain,(
    ! [B_325,C_326,A_327] :
      ( v1_tsep_1(B_325,C_326)
      | ~ r1_tarski(u1_struct_0(B_325),u1_struct_0(C_326))
      | ~ m1_pre_topc(C_326,A_327)
      | v2_struct_0(C_326)
      | ~ m1_pre_topc(B_325,A_327)
      | ~ v1_tsep_1(B_325,A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_438,plain,(
    ! [B_333,A_334,A_335] :
      ( v1_tsep_1(B_333,A_334)
      | ~ m1_pre_topc(A_334,A_335)
      | v2_struct_0(A_334)
      | ~ m1_pre_topc(B_333,A_335)
      | ~ v1_tsep_1(B_333,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335)
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(resolution,[status(thm)],[c_361,c_414])).

tff(c_444,plain,(
    ! [B_333] :
      ( v1_tsep_1(B_333,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_333,'#skF_2')
      | ~ v1_tsep_1(B_333,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_333,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_438])).

tff(c_457,plain,(
    ! [B_333] :
      ( v1_tsep_1(B_333,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_333,'#skF_2')
      | ~ v1_tsep_1(B_333,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_333,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_54,c_52,c_444])).

tff(c_478,plain,(
    ! [B_338] :
      ( v1_tsep_1(B_338,'#skF_4')
      | ~ m1_pre_topc(B_338,'#skF_2')
      | ~ v1_tsep_1(B_338,'#skF_2')
      | ~ m1_pre_topc(B_338,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46,c_457])).

tff(c_481,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_478])).

tff(c_484,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_48,c_481])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_26,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_129,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_161,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_73])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_108,plain,(
    ! [B_261,A_262] :
      ( v2_pre_topc(B_261)
      | ~ m1_pre_topc(B_261,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_108])).

tff(c_123,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_114])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_130,plain,(
    ! [B_263,A_264] :
      ( m1_subset_1(u1_struct_0(B_263),k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ m1_pre_topc(B_263,A_264)
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_134,plain,(
    ! [B_263,A_264] :
      ( r1_tarski(u1_struct_0(B_263),u1_struct_0(A_264))
      | ~ m1_pre_topc(B_263,A_264)
      | ~ l1_pre_topc(A_264) ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_185,plain,(
    ! [B_275,C_276,A_277] :
      ( v1_tsep_1(B_275,C_276)
      | ~ r1_tarski(u1_struct_0(B_275),u1_struct_0(C_276))
      | ~ m1_pre_topc(C_276,A_277)
      | v2_struct_0(C_276)
      | ~ m1_pre_topc(B_275,A_277)
      | ~ v1_tsep_1(B_275,A_277)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_193,plain,(
    ! [B_281,A_282,A_283] :
      ( v1_tsep_1(B_281,A_282)
      | ~ m1_pre_topc(A_282,A_283)
      | v2_struct_0(A_282)
      | ~ m1_pre_topc(B_281,A_283)
      | ~ v1_tsep_1(B_281,A_283)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ m1_pre_topc(B_281,A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_134,c_185])).

tff(c_199,plain,(
    ! [B_281] :
      ( v1_tsep_1(B_281,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_281,'#skF_2')
      | ~ v1_tsep_1(B_281,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_281,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_193])).

tff(c_212,plain,(
    ! [B_281] :
      ( v1_tsep_1(B_281,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_281,'#skF_2')
      | ~ v1_tsep_1(B_281,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_281,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_54,c_52,c_199])).

tff(c_244,plain,(
    ! [B_290] :
      ( v1_tsep_1(B_290,'#skF_4')
      | ~ m1_pre_topc(B_290,'#skF_2')
      | ~ v1_tsep_1(B_290,'#skF_2')
      | ~ m1_pre_topc(B_290,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46,c_212])).

tff(c_247,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_244])).

tff(c_250,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_48,c_247])).

tff(c_286,plain,(
    ! [C_301,E_298,A_300,D_302,B_299] :
      ( k3_tmap_1(A_300,B_299,C_301,D_302,E_298) = k2_partfun1(u1_struct_0(C_301),u1_struct_0(B_299),E_298,u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,C_301)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_301),u1_struct_0(B_299))))
      | ~ v1_funct_2(E_298,u1_struct_0(C_301),u1_struct_0(B_299))
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc(D_302,A_300)
      | ~ m1_pre_topc(C_301,A_300)
      | ~ l1_pre_topc(B_299)
      | ~ v2_pre_topc(B_299)
      | v2_struct_0(B_299)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_291,plain,(
    ! [A_300,D_302] :
      ( k3_tmap_1(A_300,'#skF_1','#skF_4',D_302,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_302,A_300)
      | ~ m1_pre_topc('#skF_4',A_300)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_38,c_286])).

tff(c_295,plain,(
    ! [A_300,D_302] :
      ( k3_tmap_1(A_300,'#skF_1','#skF_4',D_302,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,'#skF_4')
      | ~ m1_pre_topc(D_302,A_300)
      | ~ m1_pre_topc('#skF_4',A_300)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_291])).

tff(c_297,plain,(
    ! [A_303,D_304] :
      ( k3_tmap_1(A_303,'#skF_1','#skF_4',D_304,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_304))
      | ~ m1_pre_topc(D_304,'#skF_4')
      | ~ m1_pre_topc(D_304,A_303)
      | ~ m1_pre_topc('#skF_4',A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_295])).

tff(c_305,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_297])).

tff(c_319,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_32,c_305])).

tff(c_320,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_319])).

tff(c_227,plain,(
    ! [A_286,B_287,C_288,D_289] :
      ( k2_partfun1(u1_struct_0(A_286),u1_struct_0(B_287),C_288,u1_struct_0(D_289)) = k2_tmap_1(A_286,B_287,C_288,D_289)
      | ~ m1_pre_topc(D_289,A_286)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_286),u1_struct_0(B_287))))
      | ~ v1_funct_2(C_288,u1_struct_0(A_286),u1_struct_0(B_287))
      | ~ v1_funct_1(C_288)
      | ~ l1_pre_topc(B_287)
      | ~ v2_pre_topc(B_287)
      | v2_struct_0(B_287)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_232,plain,(
    ! [D_289] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_289)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_289)
      | ~ m1_pre_topc(D_289,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_227])).

tff(c_236,plain,(
    ! [D_289] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_289)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_289)
      | ~ m1_pre_topc(D_289,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_92,c_60,c_58,c_42,c_40,c_232])).

tff(c_237,plain,(
    ! [D_289] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_289)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_289)
      | ~ m1_pre_topc(D_289,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_62,c_236])).

tff(c_325,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_237])).

tff(c_332,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_325])).

tff(c_337,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_129])).

tff(c_20,plain,(
    ! [A_65,F_127,D_121,B_97,C_113] :
      ( r1_tmap_1(B_97,A_65,C_113,F_127)
      | ~ r1_tmap_1(D_121,A_65,k2_tmap_1(B_97,A_65,C_113,D_121),F_127)
      | ~ m1_subset_1(F_127,u1_struct_0(D_121))
      | ~ m1_subset_1(F_127,u1_struct_0(B_97))
      | ~ m1_pre_topc(D_121,B_97)
      | ~ v1_tsep_1(D_121,B_97)
      | v2_struct_0(D_121)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_97),u1_struct_0(A_65))))
      | ~ v1_funct_2(C_113,u1_struct_0(B_97),u1_struct_0(A_65))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_97)
      | ~ v2_pre_topc(B_97)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_343,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_337,c_20])).

tff(c_346,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_123,c_92,c_42,c_40,c_38,c_250,c_32,c_30,c_74,c_343])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_50,c_161,c_346])).

tff(c_349,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_578,plain,(
    ! [B_349,D_350,F_352,A_351,C_348] :
      ( r1_tmap_1(D_350,A_351,k2_tmap_1(B_349,A_351,C_348,D_350),F_352)
      | ~ r1_tmap_1(B_349,A_351,C_348,F_352)
      | ~ m1_subset_1(F_352,u1_struct_0(D_350))
      | ~ m1_subset_1(F_352,u1_struct_0(B_349))
      | ~ m1_pre_topc(D_350,B_349)
      | ~ v1_tsep_1(D_350,B_349)
      | v2_struct_0(D_350)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_349),u1_struct_0(A_351))))
      | ~ v1_funct_2(C_348,u1_struct_0(B_349),u1_struct_0(A_351))
      | ~ v1_funct_1(C_348)
      | ~ l1_pre_topc(B_349)
      | ~ v2_pre_topc(B_349)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_583,plain,(
    ! [D_350,F_352] :
      ( r1_tmap_1(D_350,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_350),F_352)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_352)
      | ~ m1_subset_1(F_352,u1_struct_0(D_350))
      | ~ m1_subset_1(F_352,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_350,'#skF_4')
      | ~ v1_tsep_1(D_350,'#skF_4')
      | v2_struct_0(D_350)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_578])).

tff(c_587,plain,(
    ! [D_350,F_352] :
      ( r1_tmap_1(D_350,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_350),F_352)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_352)
      | ~ m1_subset_1(F_352,u1_struct_0(D_350))
      | ~ m1_subset_1(F_352,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_350,'#skF_4')
      | ~ v1_tsep_1(D_350,'#skF_4')
      | v2_struct_0(D_350)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_123,c_92,c_42,c_40,c_583])).

tff(c_598,plain,(
    ! [D_354,F_355] :
      ( r1_tmap_1(D_354,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_354),F_355)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_355)
      | ~ m1_subset_1(F_355,u1_struct_0(D_354))
      | ~ m1_subset_1(F_355,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_354,'#skF_4')
      | ~ v1_tsep_1(D_354,'#skF_4')
      | v2_struct_0(D_354) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_587])).

tff(c_485,plain,(
    ! [C_342,E_339,A_341,D_343,B_340] :
      ( k3_tmap_1(A_341,B_340,C_342,D_343,E_339) = k2_partfun1(u1_struct_0(C_342),u1_struct_0(B_340),E_339,u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,C_342)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0(B_340))))
      | ~ v1_funct_2(E_339,u1_struct_0(C_342),u1_struct_0(B_340))
      | ~ v1_funct_1(E_339)
      | ~ m1_pre_topc(D_343,A_341)
      | ~ m1_pre_topc(C_342,A_341)
      | ~ l1_pre_topc(B_340)
      | ~ v2_pre_topc(B_340)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_490,plain,(
    ! [A_341,D_343] :
      ( k3_tmap_1(A_341,'#skF_1','#skF_4',D_343,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_343,A_341)
      | ~ m1_pre_topc('#skF_4',A_341)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_38,c_485])).

tff(c_494,plain,(
    ! [A_341,D_343] :
      ( k3_tmap_1(A_341,'#skF_1','#skF_4',D_343,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,'#skF_4')
      | ~ m1_pre_topc(D_343,A_341)
      | ~ m1_pre_topc('#skF_4',A_341)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_490])).

tff(c_515,plain,(
    ! [A_346,D_347] :
      ( k3_tmap_1(A_346,'#skF_1','#skF_4',D_347,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_347))
      | ~ m1_pre_topc(D_347,'#skF_4')
      | ~ m1_pre_topc(D_347,A_346)
      | ~ m1_pre_topc('#skF_4',A_346)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_494])).

tff(c_523,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_515])).

tff(c_537,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_32,c_523])).

tff(c_538,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_537])).

tff(c_418,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k2_partfun1(u1_struct_0(A_328),u1_struct_0(B_329),C_330,u1_struct_0(D_331)) = k2_tmap_1(A_328,B_329,C_330,D_331)
      | ~ m1_pre_topc(D_331,A_328)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328),u1_struct_0(B_329))))
      | ~ v1_funct_2(C_330,u1_struct_0(A_328),u1_struct_0(B_329))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc(B_329)
      | ~ v2_pre_topc(B_329)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_423,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_418])).

tff(c_427,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_92,c_60,c_58,c_42,c_40,c_423])).

tff(c_428,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_62,c_427])).

tff(c_542,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_428])).

tff(c_549,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_542])).

tff(c_350,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_556,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_350])).

tff(c_601,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_598,c_556])).

tff(c_604,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_32,c_30,c_74,c_349,c_601])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.53  
% 3.64/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.53  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.53  
% 3.64/1.53  %Foreground sorts:
% 3.64/1.53  
% 3.64/1.53  
% 3.64/1.53  %Background operators:
% 3.64/1.53  
% 3.64/1.53  
% 3.64/1.53  %Foreground operators:
% 3.64/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.64/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.64/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.64/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.64/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.53  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.64/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.64/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.64/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.64/1.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.64/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.53  
% 3.64/1.55  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.64/1.55  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.64/1.55  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.64/1.55  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.64/1.55  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.64/1.55  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.64/1.55  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.64/1.55  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.64/1.55  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.64/1.55  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_36, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_79, plain, (![B_255, A_256]: (l1_pre_topc(B_255) | ~m1_pre_topc(B_255, A_256) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.64/1.55  tff(c_85, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_79])).
% 3.64/1.55  tff(c_92, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_85])).
% 3.64/1.55  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_357, plain, (![B_310, A_311]: (m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(u1_struct_0(A_311))) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.64/1.55  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.55  tff(c_361, plain, (![B_310, A_311]: (r1_tarski(u1_struct_0(B_310), u1_struct_0(A_311)) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311))), inference(resolution, [status(thm)], [c_357, c_2])).
% 3.64/1.55  tff(c_414, plain, (![B_325, C_326, A_327]: (v1_tsep_1(B_325, C_326) | ~r1_tarski(u1_struct_0(B_325), u1_struct_0(C_326)) | ~m1_pre_topc(C_326, A_327) | v2_struct_0(C_326) | ~m1_pre_topc(B_325, A_327) | ~v1_tsep_1(B_325, A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.64/1.55  tff(c_438, plain, (![B_333, A_334, A_335]: (v1_tsep_1(B_333, A_334) | ~m1_pre_topc(A_334, A_335) | v2_struct_0(A_334) | ~m1_pre_topc(B_333, A_335) | ~v1_tsep_1(B_333, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334))), inference(resolution, [status(thm)], [c_361, c_414])).
% 3.64/1.55  tff(c_444, plain, (![B_333]: (v1_tsep_1(B_333, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_333, '#skF_2') | ~v1_tsep_1(B_333, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_333, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_438])).
% 3.64/1.55  tff(c_457, plain, (![B_333]: (v1_tsep_1(B_333, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_333, '#skF_2') | ~v1_tsep_1(B_333, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_333, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_54, c_52, c_444])).
% 3.64/1.55  tff(c_478, plain, (![B_338]: (v1_tsep_1(B_338, '#skF_4') | ~m1_pre_topc(B_338, '#skF_2') | ~v1_tsep_1(B_338, '#skF_2') | ~m1_pre_topc(B_338, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_46, c_457])).
% 3.64/1.55  tff(c_481, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_478])).
% 3.64/1.55  tff(c_484, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_48, c_481])).
% 3.64/1.55  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_26, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.64/1.55  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_70, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 3.64/1.55  tff(c_129, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 3.64/1.55  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_73, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 3.64/1.55  tff(c_161, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_73])).
% 3.64/1.55  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_108, plain, (![B_261, A_262]: (v2_pre_topc(B_261) | ~m1_pre_topc(B_261, A_262) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.55  tff(c_114, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_108])).
% 3.64/1.55  tff(c_123, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_114])).
% 3.64/1.55  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.64/1.55  tff(c_130, plain, (![B_263, A_264]: (m1_subset_1(u1_struct_0(B_263), k1_zfmisc_1(u1_struct_0(A_264))) | ~m1_pre_topc(B_263, A_264) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.64/1.55  tff(c_134, plain, (![B_263, A_264]: (r1_tarski(u1_struct_0(B_263), u1_struct_0(A_264)) | ~m1_pre_topc(B_263, A_264) | ~l1_pre_topc(A_264))), inference(resolution, [status(thm)], [c_130, c_2])).
% 3.64/1.55  tff(c_185, plain, (![B_275, C_276, A_277]: (v1_tsep_1(B_275, C_276) | ~r1_tarski(u1_struct_0(B_275), u1_struct_0(C_276)) | ~m1_pre_topc(C_276, A_277) | v2_struct_0(C_276) | ~m1_pre_topc(B_275, A_277) | ~v1_tsep_1(B_275, A_277) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.64/1.55  tff(c_193, plain, (![B_281, A_282, A_283]: (v1_tsep_1(B_281, A_282) | ~m1_pre_topc(A_282, A_283) | v2_struct_0(A_282) | ~m1_pre_topc(B_281, A_283) | ~v1_tsep_1(B_281, A_283) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~m1_pre_topc(B_281, A_282) | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_134, c_185])).
% 3.64/1.55  tff(c_199, plain, (![B_281]: (v1_tsep_1(B_281, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_281, '#skF_2') | ~v1_tsep_1(B_281, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_281, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_193])).
% 3.64/1.55  tff(c_212, plain, (![B_281]: (v1_tsep_1(B_281, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_281, '#skF_2') | ~v1_tsep_1(B_281, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_281, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_54, c_52, c_199])).
% 3.64/1.55  tff(c_244, plain, (![B_290]: (v1_tsep_1(B_290, '#skF_4') | ~m1_pre_topc(B_290, '#skF_2') | ~v1_tsep_1(B_290, '#skF_2') | ~m1_pre_topc(B_290, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_46, c_212])).
% 3.64/1.55  tff(c_247, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_244])).
% 3.64/1.55  tff(c_250, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_48, c_247])).
% 3.64/1.55  tff(c_286, plain, (![C_301, E_298, A_300, D_302, B_299]: (k3_tmap_1(A_300, B_299, C_301, D_302, E_298)=k2_partfun1(u1_struct_0(C_301), u1_struct_0(B_299), E_298, u1_struct_0(D_302)) | ~m1_pre_topc(D_302, C_301) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_301), u1_struct_0(B_299)))) | ~v1_funct_2(E_298, u1_struct_0(C_301), u1_struct_0(B_299)) | ~v1_funct_1(E_298) | ~m1_pre_topc(D_302, A_300) | ~m1_pre_topc(C_301, A_300) | ~l1_pre_topc(B_299) | ~v2_pre_topc(B_299) | v2_struct_0(B_299) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.64/1.55  tff(c_291, plain, (![A_300, D_302]: (k3_tmap_1(A_300, '#skF_1', '#skF_4', D_302, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_302)) | ~m1_pre_topc(D_302, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_302, A_300) | ~m1_pre_topc('#skF_4', A_300) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(resolution, [status(thm)], [c_38, c_286])).
% 3.64/1.55  tff(c_295, plain, (![A_300, D_302]: (k3_tmap_1(A_300, '#skF_1', '#skF_4', D_302, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_302)) | ~m1_pre_topc(D_302, '#skF_4') | ~m1_pre_topc(D_302, A_300) | ~m1_pre_topc('#skF_4', A_300) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_291])).
% 3.64/1.55  tff(c_297, plain, (![A_303, D_304]: (k3_tmap_1(A_303, '#skF_1', '#skF_4', D_304, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_304)) | ~m1_pre_topc(D_304, '#skF_4') | ~m1_pre_topc(D_304, A_303) | ~m1_pre_topc('#skF_4', A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(negUnitSimplification, [status(thm)], [c_62, c_295])).
% 3.64/1.55  tff(c_305, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_297])).
% 3.64/1.55  tff(c_319, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_32, c_305])).
% 3.64/1.55  tff(c_320, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_319])).
% 3.64/1.55  tff(c_227, plain, (![A_286, B_287, C_288, D_289]: (k2_partfun1(u1_struct_0(A_286), u1_struct_0(B_287), C_288, u1_struct_0(D_289))=k2_tmap_1(A_286, B_287, C_288, D_289) | ~m1_pre_topc(D_289, A_286) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_286), u1_struct_0(B_287)))) | ~v1_funct_2(C_288, u1_struct_0(A_286), u1_struct_0(B_287)) | ~v1_funct_1(C_288) | ~l1_pre_topc(B_287) | ~v2_pre_topc(B_287) | v2_struct_0(B_287) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.64/1.55  tff(c_232, plain, (![D_289]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_289))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_289) | ~m1_pre_topc(D_289, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_227])).
% 3.64/1.55  tff(c_236, plain, (![D_289]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_289))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_289) | ~m1_pre_topc(D_289, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_92, c_60, c_58, c_42, c_40, c_232])).
% 3.79/1.55  tff(c_237, plain, (![D_289]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_289))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_289) | ~m1_pre_topc(D_289, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_62, c_236])).
% 3.79/1.55  tff(c_325, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_320, c_237])).
% 3.79/1.55  tff(c_332, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_325])).
% 3.79/1.55  tff(c_337, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_129])).
% 3.79/1.55  tff(c_20, plain, (![A_65, F_127, D_121, B_97, C_113]: (r1_tmap_1(B_97, A_65, C_113, F_127) | ~r1_tmap_1(D_121, A_65, k2_tmap_1(B_97, A_65, C_113, D_121), F_127) | ~m1_subset_1(F_127, u1_struct_0(D_121)) | ~m1_subset_1(F_127, u1_struct_0(B_97)) | ~m1_pre_topc(D_121, B_97) | ~v1_tsep_1(D_121, B_97) | v2_struct_0(D_121) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_97), u1_struct_0(A_65)))) | ~v1_funct_2(C_113, u1_struct_0(B_97), u1_struct_0(A_65)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_97) | ~v2_pre_topc(B_97) | v2_struct_0(B_97) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.79/1.55  tff(c_343, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_337, c_20])).
% 3.79/1.55  tff(c_346, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_123, c_92, c_42, c_40, c_38, c_250, c_32, c_30, c_74, c_343])).
% 3.79/1.55  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_50, c_161, c_346])).
% 3.79/1.55  tff(c_349, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 3.79/1.55  tff(c_578, plain, (![B_349, D_350, F_352, A_351, C_348]: (r1_tmap_1(D_350, A_351, k2_tmap_1(B_349, A_351, C_348, D_350), F_352) | ~r1_tmap_1(B_349, A_351, C_348, F_352) | ~m1_subset_1(F_352, u1_struct_0(D_350)) | ~m1_subset_1(F_352, u1_struct_0(B_349)) | ~m1_pre_topc(D_350, B_349) | ~v1_tsep_1(D_350, B_349) | v2_struct_0(D_350) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_349), u1_struct_0(A_351)))) | ~v1_funct_2(C_348, u1_struct_0(B_349), u1_struct_0(A_351)) | ~v1_funct_1(C_348) | ~l1_pre_topc(B_349) | ~v2_pre_topc(B_349) | v2_struct_0(B_349) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.79/1.55  tff(c_583, plain, (![D_350, F_352]: (r1_tmap_1(D_350, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_350), F_352) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_352) | ~m1_subset_1(F_352, u1_struct_0(D_350)) | ~m1_subset_1(F_352, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_350, '#skF_4') | ~v1_tsep_1(D_350, '#skF_4') | v2_struct_0(D_350) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_578])).
% 3.79/1.55  tff(c_587, plain, (![D_350, F_352]: (r1_tmap_1(D_350, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_350), F_352) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_352) | ~m1_subset_1(F_352, u1_struct_0(D_350)) | ~m1_subset_1(F_352, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_350, '#skF_4') | ~v1_tsep_1(D_350, '#skF_4') | v2_struct_0(D_350) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_123, c_92, c_42, c_40, c_583])).
% 3.79/1.55  tff(c_598, plain, (![D_354, F_355]: (r1_tmap_1(D_354, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_354), F_355) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_355) | ~m1_subset_1(F_355, u1_struct_0(D_354)) | ~m1_subset_1(F_355, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_354, '#skF_4') | ~v1_tsep_1(D_354, '#skF_4') | v2_struct_0(D_354))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_587])).
% 3.79/1.55  tff(c_485, plain, (![C_342, E_339, A_341, D_343, B_340]: (k3_tmap_1(A_341, B_340, C_342, D_343, E_339)=k2_partfun1(u1_struct_0(C_342), u1_struct_0(B_340), E_339, u1_struct_0(D_343)) | ~m1_pre_topc(D_343, C_342) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0(B_340)))) | ~v1_funct_2(E_339, u1_struct_0(C_342), u1_struct_0(B_340)) | ~v1_funct_1(E_339) | ~m1_pre_topc(D_343, A_341) | ~m1_pre_topc(C_342, A_341) | ~l1_pre_topc(B_340) | ~v2_pre_topc(B_340) | v2_struct_0(B_340) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.79/1.55  tff(c_490, plain, (![A_341, D_343]: (k3_tmap_1(A_341, '#skF_1', '#skF_4', D_343, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_343)) | ~m1_pre_topc(D_343, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_343, A_341) | ~m1_pre_topc('#skF_4', A_341) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(resolution, [status(thm)], [c_38, c_485])).
% 3.79/1.55  tff(c_494, plain, (![A_341, D_343]: (k3_tmap_1(A_341, '#skF_1', '#skF_4', D_343, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_343)) | ~m1_pre_topc(D_343, '#skF_4') | ~m1_pre_topc(D_343, A_341) | ~m1_pre_topc('#skF_4', A_341) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_490])).
% 3.79/1.55  tff(c_515, plain, (![A_346, D_347]: (k3_tmap_1(A_346, '#skF_1', '#skF_4', D_347, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_347)) | ~m1_pre_topc(D_347, '#skF_4') | ~m1_pre_topc(D_347, A_346) | ~m1_pre_topc('#skF_4', A_346) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(negUnitSimplification, [status(thm)], [c_62, c_494])).
% 3.79/1.55  tff(c_523, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_515])).
% 3.79/1.55  tff(c_537, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_32, c_523])).
% 3.79/1.55  tff(c_538, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_537])).
% 3.79/1.55  tff(c_418, plain, (![A_328, B_329, C_330, D_331]: (k2_partfun1(u1_struct_0(A_328), u1_struct_0(B_329), C_330, u1_struct_0(D_331))=k2_tmap_1(A_328, B_329, C_330, D_331) | ~m1_pre_topc(D_331, A_328) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328), u1_struct_0(B_329)))) | ~v1_funct_2(C_330, u1_struct_0(A_328), u1_struct_0(B_329)) | ~v1_funct_1(C_330) | ~l1_pre_topc(B_329) | ~v2_pre_topc(B_329) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.79/1.55  tff(c_423, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_418])).
% 3.79/1.55  tff(c_427, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_92, c_60, c_58, c_42, c_40, c_423])).
% 3.79/1.55  tff(c_428, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_62, c_427])).
% 3.79/1.55  tff(c_542, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_538, c_428])).
% 3.79/1.55  tff(c_549, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_542])).
% 3.79/1.55  tff(c_350, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 3.79/1.55  tff(c_556, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_350])).
% 3.79/1.55  tff(c_601, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_598, c_556])).
% 3.79/1.55  tff(c_604, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_32, c_30, c_74, c_349, c_601])).
% 3.79/1.55  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_604])).
% 3.79/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.55  
% 3.79/1.55  Inference rules
% 3.79/1.55  ----------------------
% 3.79/1.55  #Ref     : 0
% 3.79/1.55  #Sup     : 98
% 3.79/1.55  #Fact    : 0
% 3.79/1.55  #Define  : 0
% 3.79/1.55  #Split   : 5
% 3.79/1.55  #Chain   : 0
% 3.79/1.55  #Close   : 0
% 3.79/1.55  
% 3.79/1.55  Ordering : KBO
% 3.79/1.55  
% 3.79/1.55  Simplification rules
% 3.79/1.55  ----------------------
% 3.79/1.55  #Subsume      : 11
% 3.79/1.55  #Demod        : 190
% 3.79/1.55  #Tautology    : 39
% 3.79/1.55  #SimpNegUnit  : 29
% 3.79/1.55  #BackRed      : 4
% 3.79/1.55  
% 3.79/1.55  #Partial instantiations: 0
% 3.79/1.55  #Strategies tried      : 1
% 3.79/1.55  
% 3.79/1.55  Timing (in seconds)
% 3.79/1.55  ----------------------
% 3.79/1.56  Preprocessing        : 0.41
% 3.79/1.56  Parsing              : 0.22
% 3.79/1.56  CNF conversion       : 0.05
% 3.79/1.56  Main loop            : 0.35
% 3.79/1.56  Inferencing          : 0.12
% 3.79/1.56  Reduction            : 0.12
% 3.79/1.56  Demodulation         : 0.09
% 3.79/1.56  BG Simplification    : 0.02
% 3.79/1.56  Subsumption          : 0.07
% 3.79/1.56  Abstraction          : 0.02
% 3.79/1.56  MUC search           : 0.00
% 3.79/1.56  Cooper               : 0.00
% 3.79/1.56  Total                : 0.81
% 3.79/1.56  Index Insertion      : 0.00
% 3.79/1.56  Index Deletion       : 0.00
% 3.79/1.56  Index Matching       : 0.00
% 3.79/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
