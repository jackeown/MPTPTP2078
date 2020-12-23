%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 801 expanded)
%              Number of leaves         :   40 ( 300 expanded)
%              Depth                    :   12
%              Number of atoms          :  287 (3880 expanded)
%              Number of equality atoms :   15 ( 435 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_106,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> ( v1_tsep_1(C,A)
                    & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_179,axiom,(
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

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_155,plain,(
    ! [B_292,A_293] :
      ( v2_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_164,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_171,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_164])).

tff(c_113,plain,(
    ! [B_289,A_290] :
      ( l1_pre_topc(B_289)
      | ~ m1_pre_topc(B_289,A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_129,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122])).

tff(c_32,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_113])).

tff(c_126,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_119])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_287] :
      ( u1_struct_0(A_287) = k2_struct_0(A_287)
      | ~ l1_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_93])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_138,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_306,plain,(
    ! [A_304,B_305] :
      ( m1_pre_topc(A_304,B_305)
      | ~ m1_pre_topc(A_304,g1_pre_topc(u1_struct_0(B_305),u1_pre_topc(B_305)))
      | ~ l1_pre_topc(B_305)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_312,plain,(
    ! [A_304] :
      ( m1_pre_topc(A_304,'#skF_3')
      | ~ m1_pre_topc(A_304,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_306])).

tff(c_326,plain,(
    ! [A_304] :
      ( m1_pre_topc(A_304,'#skF_3')
      | ~ m1_pre_topc(A_304,'#skF_4')
      | ~ l1_pre_topc(A_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_138,c_312])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_93])).

tff(c_173,plain,(
    ! [B_294,A_295] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_185,plain,(
    ! [B_294] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_294,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_173])).

tff(c_259,plain,(
    ! [B_302] :
      ( m1_subset_1(u1_struct_0(B_302),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_302,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_185])).

tff(c_262,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_259])).

tff(c_511,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_514,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_326,c_511])).

tff(c_517,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_514])).

tff(c_520,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_517])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_520])).

tff(c_526,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_527,plain,(
    ! [A_312,B_313] :
      ( m1_pre_topc(A_312,g1_pre_topc(u1_struct_0(B_313),u1_pre_topc(B_313)))
      | ~ m1_pre_topc(A_312,B_313)
      | ~ l1_pre_topc(B_313)
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_548,plain,(
    ! [A_312] :
      ( m1_pre_topc(A_312,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_312,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_527])).

tff(c_585,plain,(
    ! [A_314] :
      ( m1_pre_topc(A_314,'#skF_4')
      | ~ m1_pre_topc(A_314,'#skF_3')
      | ~ l1_pre_topc(A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_138,c_548])).

tff(c_588,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_526,c_585])).

tff(c_605,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_588])).

tff(c_14,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_719,plain,(
    ! [B_317,A_318] :
      ( v1_tsep_1(B_317,A_318)
      | ~ v3_pre_topc(u1_struct_0(B_317),A_318)
      | ~ m1_subset_1(u1_struct_0(B_317),k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1542,plain,(
    ! [B_363,A_364] :
      ( v1_tsep_1(B_363,A_364)
      | ~ v3_pre_topc(u1_struct_0(B_363),A_364)
      | ~ v2_pre_topc(A_364)
      | ~ m1_pre_topc(B_363,A_364)
      | ~ l1_pre_topc(A_364) ) ),
    inference(resolution,[status(thm)],[c_30,c_719])).

tff(c_1588,plain,(
    ! [A_368] :
      ( v1_tsep_1('#skF_4',A_368)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_368)
      | ~ v2_pre_topc(A_368)
      | ~ m1_pre_topc('#skF_4',A_368)
      | ~ l1_pre_topc(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1542])).

tff(c_1595,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1588])).

tff(c_1599,plain,(
    v1_tsep_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_129,c_605,c_1595])).

tff(c_161,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_155])).

tff(c_168,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_161])).

tff(c_1605,plain,(
    ! [B_370,A_371] :
      ( v1_tsep_1(B_370,A_371)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(B_370),u1_pre_topc(B_370)),A_371)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(B_370),u1_pre_topc(B_370)),A_371)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_370),u1_pre_topc(B_370)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(B_370),u1_pre_topc(B_370)))
      | ~ l1_pre_topc(B_370)
      | ~ v2_pre_topc(B_370)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1614,plain,(
    ! [A_371] :
      ( v1_tsep_1('#skF_3',A_371)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_371)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_371)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1605])).

tff(c_1625,plain,(
    ! [A_371] :
      ( v1_tsep_1('#skF_3',A_371)
      | ~ m1_pre_topc('#skF_4',A_371)
      | ~ v1_tsep_1('#skF_4',A_371)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_171,c_138,c_133,c_129,c_138,c_133,c_138,c_138,c_133,c_1614])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_94,plain,(
    ! [A_288] :
      ( u1_struct_0(A_288) = k2_struct_0(A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_148,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_52])).

tff(c_172,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_602,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_585])).

tff(c_615,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_602])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_149,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_139,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_1981,plain,(
    ! [C_396,G_397,B_398,A_395,D_400,E_399] :
      ( r1_tmap_1(D_400,B_398,E_399,G_397)
      | ~ r1_tmap_1(C_396,B_398,k3_tmap_1(A_395,B_398,D_400,C_396,E_399),G_397)
      | ~ m1_subset_1(G_397,u1_struct_0(C_396))
      | ~ m1_subset_1(G_397,u1_struct_0(D_400))
      | ~ m1_pre_topc(C_396,D_400)
      | ~ v1_tsep_1(C_396,D_400)
      | ~ m1_subset_1(E_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_400),u1_struct_0(B_398))))
      | ~ v1_funct_2(E_399,u1_struct_0(D_400),u1_struct_0(B_398))
      | ~ v1_funct_1(E_399)
      | ~ m1_pre_topc(D_400,A_395)
      | v2_struct_0(D_400)
      | ~ m1_pre_topc(C_396,A_395)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc(B_398)
      | ~ v2_pre_topc(B_398)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1983,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_1981])).

tff(c_1986,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_148,c_102,c_137,c_172,c_102,c_137,c_615,c_149,c_137,c_139,c_133,c_1983])).

tff(c_1987,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_1986])).

tff(c_1990,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1625,c_1987])).

tff(c_1994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_129,c_1599,c_605,c_1990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.91  
% 4.85/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.91  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.85/1.91  
% 4.85/1.91  %Foreground sorts:
% 4.85/1.91  
% 4.85/1.91  
% 4.85/1.91  %Background operators:
% 4.85/1.91  
% 4.85/1.91  
% 4.85/1.91  %Foreground operators:
% 4.85/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.85/1.91  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.85/1.91  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.85/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/1.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.85/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.91  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.85/1.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.85/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.85/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.85/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.85/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.85/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.85/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.85/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.91  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.85/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.85/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.85/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.85/1.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.85/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.91  
% 4.85/1.93  tff(f_228, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.85/1.93  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.85/1.93  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.85/1.93  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.85/1.93  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.85/1.93  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.85/1.93  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.85/1.93  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.85/1.93  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.85/1.93  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.85/1.93  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tmap_1)).
% 4.85/1.93  tff(f_179, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.85/1.93  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_155, plain, (![B_292, A_293]: (v2_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.85/1.93  tff(c_164, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_155])).
% 4.85/1.93  tff(c_171, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_164])).
% 4.85/1.93  tff(c_113, plain, (![B_289, A_290]: (l1_pre_topc(B_289) | ~m1_pre_topc(B_289, A_290) | ~l1_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.85/1.93  tff(c_122, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_113])).
% 4.85/1.93  tff(c_129, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_122])).
% 4.85/1.93  tff(c_32, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.85/1.93  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_119, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_113])).
% 4.85/1.93  tff(c_126, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_119])).
% 4.85/1.93  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.85/1.93  tff(c_89, plain, (![A_287]: (u1_struct_0(A_287)=k2_struct_0(A_287) | ~l1_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.85/1.93  tff(c_93, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_89])).
% 4.85/1.93  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_126, c_93])).
% 4.85/1.93  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_138, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 4.85/1.93  tff(c_306, plain, (![A_304, B_305]: (m1_pre_topc(A_304, B_305) | ~m1_pre_topc(A_304, g1_pre_topc(u1_struct_0(B_305), u1_pre_topc(B_305))) | ~l1_pre_topc(B_305) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.85/1.93  tff(c_312, plain, (![A_304]: (m1_pre_topc(A_304, '#skF_3') | ~m1_pre_topc(A_304, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_304))), inference(superposition, [status(thm), theory('equality')], [c_133, c_306])).
% 4.85/1.93  tff(c_326, plain, (![A_304]: (m1_pre_topc(A_304, '#skF_3') | ~m1_pre_topc(A_304, '#skF_4') | ~l1_pre_topc(A_304))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_138, c_312])).
% 4.85/1.93  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_129, c_93])).
% 4.85/1.93  tff(c_173, plain, (![B_294, A_295]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(u1_struct_0(A_295))) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/1.93  tff(c_185, plain, (![B_294]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_294, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_173])).
% 4.85/1.93  tff(c_259, plain, (![B_302]: (m1_subset_1(u1_struct_0(B_302), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_302, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_185])).
% 4.85/1.93  tff(c_262, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_259])).
% 4.85/1.93  tff(c_511, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_262])).
% 4.85/1.93  tff(c_514, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_326, c_511])).
% 4.85/1.93  tff(c_517, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_514])).
% 4.85/1.93  tff(c_520, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_517])).
% 4.85/1.93  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_520])).
% 4.85/1.93  tff(c_526, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_262])).
% 4.85/1.93  tff(c_527, plain, (![A_312, B_313]: (m1_pre_topc(A_312, g1_pre_topc(u1_struct_0(B_313), u1_pre_topc(B_313))) | ~m1_pre_topc(A_312, B_313) | ~l1_pre_topc(B_313) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.85/1.93  tff(c_548, plain, (![A_312]: (m1_pre_topc(A_312, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_312, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_312))), inference(superposition, [status(thm), theory('equality')], [c_133, c_527])).
% 4.85/1.93  tff(c_585, plain, (![A_314]: (m1_pre_topc(A_314, '#skF_4') | ~m1_pre_topc(A_314, '#skF_3') | ~l1_pre_topc(A_314))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_138, c_548])).
% 4.85/1.93  tff(c_588, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_526, c_585])).
% 4.85/1.93  tff(c_605, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_588])).
% 4.85/1.93  tff(c_14, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.85/1.93  tff(c_30, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/1.93  tff(c_719, plain, (![B_317, A_318]: (v1_tsep_1(B_317, A_318) | ~v3_pre_topc(u1_struct_0(B_317), A_318) | ~m1_subset_1(u1_struct_0(B_317), k1_zfmisc_1(u1_struct_0(A_318))) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.85/1.93  tff(c_1542, plain, (![B_363, A_364]: (v1_tsep_1(B_363, A_364) | ~v3_pre_topc(u1_struct_0(B_363), A_364) | ~v2_pre_topc(A_364) | ~m1_pre_topc(B_363, A_364) | ~l1_pre_topc(A_364))), inference(resolution, [status(thm)], [c_30, c_719])).
% 4.85/1.93  tff(c_1588, plain, (![A_368]: (v1_tsep_1('#skF_4', A_368) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_368) | ~v2_pre_topc(A_368) | ~m1_pre_topc('#skF_4', A_368) | ~l1_pre_topc(A_368))), inference(superposition, [status(thm), theory('equality')], [c_137, c_1542])).
% 4.85/1.93  tff(c_1595, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_1588])).
% 4.85/1.93  tff(c_1599, plain, (v1_tsep_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_129, c_605, c_1595])).
% 4.85/1.93  tff(c_161, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_155])).
% 4.85/1.93  tff(c_168, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_161])).
% 4.85/1.93  tff(c_1605, plain, (![B_370, A_371]: (v1_tsep_1(B_370, A_371) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(B_370), u1_pre_topc(B_370)), A_371) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(B_370), u1_pre_topc(B_370)), A_371) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_370), u1_pre_topc(B_370))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(B_370), u1_pre_topc(B_370))) | ~l1_pre_topc(B_370) | ~v2_pre_topc(B_370) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.85/1.93  tff(c_1614, plain, (![A_371]: (v1_tsep_1('#skF_3', A_371) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_371) | ~v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_371) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1605])).
% 4.85/1.93  tff(c_1625, plain, (![A_371]: (v1_tsep_1('#skF_3', A_371) | ~m1_pre_topc('#skF_4', A_371) | ~v1_tsep_1('#skF_4', A_371) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_171, c_138, c_133, c_129, c_138, c_133, c_138, c_138, c_133, c_1614])).
% 4.85/1.93  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_94, plain, (![A_288]: (u1_struct_0(A_288)=k2_struct_0(A_288) | ~l1_pre_topc(A_288))), inference(resolution, [status(thm)], [c_6, c_89])).
% 4.85/1.93  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_94])).
% 4.85/1.93  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54])).
% 4.85/1.93  tff(c_148, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 4.85/1.93  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_52])).
% 4.85/1.93  tff(c_172, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 4.85/1.93  tff(c_602, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_585])).
% 4.85/1.93  tff(c_615, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_602])).
% 4.85/1.93  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_149, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48])).
% 4.85/1.93  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 4.85/1.93  tff(c_139, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_77])).
% 4.85/1.93  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_228])).
% 4.85/1.93  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 4.85/1.93  tff(c_1981, plain, (![C_396, G_397, B_398, A_395, D_400, E_399]: (r1_tmap_1(D_400, B_398, E_399, G_397) | ~r1_tmap_1(C_396, B_398, k3_tmap_1(A_395, B_398, D_400, C_396, E_399), G_397) | ~m1_subset_1(G_397, u1_struct_0(C_396)) | ~m1_subset_1(G_397, u1_struct_0(D_400)) | ~m1_pre_topc(C_396, D_400) | ~v1_tsep_1(C_396, D_400) | ~m1_subset_1(E_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_400), u1_struct_0(B_398)))) | ~v1_funct_2(E_399, u1_struct_0(D_400), u1_struct_0(B_398)) | ~v1_funct_1(E_399) | ~m1_pre_topc(D_400, A_395) | v2_struct_0(D_400) | ~m1_pre_topc(C_396, A_395) | v2_struct_0(C_396) | ~l1_pre_topc(B_398) | ~v2_pre_topc(B_398) | v2_struct_0(B_398) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.85/1.93  tff(c_1983, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_1981])).
% 4.85/1.93  tff(c_1986, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_148, c_102, c_137, c_172, c_102, c_137, c_615, c_149, c_137, c_139, c_133, c_1983])).
% 4.85/1.93  tff(c_1987, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_1986])).
% 4.85/1.93  tff(c_1990, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1625, c_1987])).
% 4.85/1.93  tff(c_1994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_129, c_1599, c_605, c_1990])).
% 4.85/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.93  
% 4.85/1.93  Inference rules
% 4.85/1.93  ----------------------
% 4.85/1.93  #Ref     : 0
% 4.85/1.93  #Sup     : 380
% 4.85/1.93  #Fact    : 0
% 4.85/1.93  #Define  : 0
% 4.85/1.93  #Split   : 17
% 4.85/1.93  #Chain   : 0
% 4.85/1.93  #Close   : 0
% 4.85/1.93  
% 4.85/1.93  Ordering : KBO
% 4.85/1.93  
% 4.85/1.93  Simplification rules
% 4.85/1.93  ----------------------
% 4.85/1.93  #Subsume      : 101
% 4.85/1.93  #Demod        : 625
% 4.85/1.93  #Tautology    : 113
% 4.85/1.93  #SimpNegUnit  : 17
% 4.85/1.93  #BackRed      : 6
% 4.85/1.93  
% 4.85/1.93  #Partial instantiations: 0
% 4.85/1.93  #Strategies tried      : 1
% 4.85/1.93  
% 4.85/1.93  Timing (in seconds)
% 4.85/1.93  ----------------------
% 4.85/1.93  Preprocessing        : 0.42
% 4.85/1.93  Parsing              : 0.21
% 4.85/1.93  CNF conversion       : 0.05
% 4.85/1.93  Main loop            : 0.65
% 4.85/1.93  Inferencing          : 0.20
% 4.85/1.93  Reduction            : 0.25
% 4.85/1.93  Demodulation         : 0.19
% 4.85/1.93  BG Simplification    : 0.03
% 4.85/1.93  Subsumption          : 0.12
% 4.85/1.93  Abstraction          : 0.02
% 4.85/1.93  MUC search           : 0.00
% 4.85/1.94  Cooper               : 0.00
% 4.85/1.94  Total                : 1.12
% 4.85/1.94  Index Insertion      : 0.00
% 4.85/1.94  Index Deletion       : 0.00
% 4.85/1.94  Index Matching       : 0.00
% 4.85/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
