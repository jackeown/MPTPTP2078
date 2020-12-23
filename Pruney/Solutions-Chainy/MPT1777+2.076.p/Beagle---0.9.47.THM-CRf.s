%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  145 (1085 expanded)
%              Number of leaves         :   43 ( 393 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 (5117 expanded)
%              Number of equality atoms :   14 ( 552 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_249,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_200,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_113,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_158,plain,(
    ! [B_302,A_303] :
      ( v2_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_164,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_158])).

tff(c_171,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_164])).

tff(c_114,plain,(
    ! [B_299,A_300] :
      ( l1_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_127,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_120])).

tff(c_30,plain,(
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_297] :
      ( u1_struct_0(A_297) = k2_struct_0(A_297)
      | ~ l1_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_135,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_95])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_140,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_52])).

tff(c_413,plain,(
    ! [A_319,B_320] :
      ( m1_pre_topc(A_319,g1_pre_topc(u1_struct_0(B_320),u1_pre_topc(B_320)))
      | ~ m1_pre_topc(A_319,B_320)
      | ~ l1_pre_topc(B_320)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_430,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_319,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_413])).

tff(c_464,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,'#skF_4')
      | ~ m1_pre_topc(A_321,'#skF_3')
      | ~ l1_pre_topc(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_140,c_430])).

tff(c_475,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_464])).

tff(c_482,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_475])).

tff(c_251,plain,(
    ! [B_309,A_310] :
      ( m1_pre_topc(B_309,A_310)
      | ~ m1_pre_topc(B_309,g1_pre_topc(u1_struct_0(A_310),u1_pre_topc(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_257,plain,(
    ! [B_309] :
      ( m1_pre_topc(B_309,'#skF_3')
      | ~ m1_pre_topc(B_309,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_251])).

tff(c_271,plain,(
    ! [B_309] :
      ( m1_pre_topc(B_309,'#skF_3')
      | ~ m1_pre_topc(B_309,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_140,c_257])).

tff(c_175,plain,(
    ! [B_304,A_305] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_187,plain,(
    ! [B_304] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_304,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_175])).

tff(c_307,plain,(
    ! [B_314] :
      ( m1_subset_1(u1_struct_0(B_314),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_314,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_187])).

tff(c_313,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_307])).

tff(c_640,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_647,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_640])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_647])).

tff(c_659,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_123])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_95])).

tff(c_181,plain,(
    ! [B_304] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_304,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_175])).

tff(c_208,plain,(
    ! [B_306] :
      ( m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_306,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_181])).

tff(c_211,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_208])).

tff(c_320,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_323,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_323])).

tff(c_329,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_32,plain,(
    ! [B_38,C_40,A_34] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0(C_40))
      | ~ m1_pre_topc(B_38,C_40)
      | ~ m1_pre_topc(C_40,A_34)
      | ~ m1_pre_topc(B_38,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_661,plain,(
    ! [B_38] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_659,c_32])).

tff(c_686,plain,(
    ! [B_331] :
      ( r1_tarski(u1_struct_0(B_331),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_331,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_127,c_135,c_661])).

tff(c_689,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_686])).

tff(c_742,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_745,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_742])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_745])).

tff(c_751,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_16,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_792,plain,(
    ! [B_334,A_335] :
      ( v1_tsep_1(B_334,A_335)
      | ~ v3_pre_topc(u1_struct_0(B_334),A_335)
      | ~ m1_subset_1(u1_struct_0(B_334),k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ m1_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1612,plain,(
    ! [B_385,A_386] :
      ( v1_tsep_1(B_385,A_386)
      | ~ v3_pre_topc(u1_struct_0(B_385),A_386)
      | ~ v2_pre_topc(A_386)
      | ~ m1_pre_topc(B_385,A_386)
      | ~ l1_pre_topc(A_386) ) ),
    inference(resolution,[status(thm)],[c_28,c_792])).

tff(c_1756,plain,(
    ! [A_398] :
      ( v1_tsep_1('#skF_3',A_398)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_398)
      | ~ v2_pre_topc(A_398)
      | ~ m1_pre_topc('#skF_3',A_398)
      | ~ l1_pre_topc(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1612])).

tff(c_1763,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1756])).

tff(c_1767,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_127,c_659,c_1763])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_96,plain,(
    ! [A_298] :
      ( u1_struct_0(A_298) = k2_struct_0(A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_104,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56])).

tff(c_148,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_109])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_146,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_54])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_149,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_141,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_79])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1092,plain,(
    ! [D_351,C_350,G_352,A_349,E_348,B_353] :
      ( r1_tmap_1(D_351,B_353,E_348,G_352)
      | ~ r1_tmap_1(C_350,B_353,k3_tmap_1(A_349,B_353,D_351,C_350,E_348),G_352)
      | ~ m1_subset_1(G_352,u1_struct_0(C_350))
      | ~ m1_subset_1(G_352,u1_struct_0(D_351))
      | ~ m1_pre_topc(C_350,D_351)
      | ~ v1_tsep_1(C_350,D_351)
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_351),u1_struct_0(B_353))))
      | ~ v1_funct_2(E_348,u1_struct_0(D_351),u1_struct_0(B_353))
      | ~ v1_funct_1(E_348)
      | ~ m1_pre_topc(D_351,A_349)
      | v2_struct_0(D_351)
      | ~ m1_pre_topc(C_350,A_349)
      | v2_struct_0(C_350)
      | ~ l1_pre_topc(B_353)
      | ~ v2_pre_topc(B_353)
      | v2_struct_0(B_353)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1094,plain,
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
    inference(resolution,[status(thm)],[c_80,c_1092])).

tff(c_1097,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_148,c_104,c_139,c_147,c_104,c_139,c_482,c_149,c_139,c_141,c_135,c_1094])).

tff(c_1098,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1097])).

tff(c_167,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_158])).

tff(c_174,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_167])).

tff(c_544,plain,(
    ! [B_323,C_324,A_325] :
      ( r1_tarski(u1_struct_0(B_323),u1_struct_0(C_324))
      | ~ m1_pre_topc(B_323,C_324)
      | ~ m1_pre_topc(C_324,A_325)
      | ~ m1_pre_topc(B_323,A_325)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_554,plain,(
    ! [B_323] :
      ( r1_tarski(u1_struct_0(B_323),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_323,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_329,c_544])).

tff(c_605,plain,(
    ! [B_327] :
      ( r1_tarski(u1_struct_0(B_327),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_327,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_130,c_139,c_554])).

tff(c_611,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_605])).

tff(c_621,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_611])).

tff(c_878,plain,(
    ! [B_337,C_338,A_339] :
      ( v1_tsep_1(B_337,C_338)
      | ~ r1_tarski(u1_struct_0(B_337),u1_struct_0(C_338))
      | ~ m1_pre_topc(C_338,A_339)
      | v2_struct_0(C_338)
      | ~ m1_pre_topc(B_337,A_339)
      | ~ v1_tsep_1(B_337,A_339)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_882,plain,(
    ! [B_337,A_339] :
      ( v1_tsep_1(B_337,'#skF_4')
      | ~ r1_tarski(u1_struct_0(B_337),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_339)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_337,A_339)
      | ~ v1_tsep_1(B_337,A_339)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_878])).

tff(c_1569,plain,(
    ! [B_381,A_382] :
      ( v1_tsep_1(B_381,'#skF_4')
      | ~ r1_tarski(u1_struct_0(B_381),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_382)
      | ~ m1_pre_topc(B_381,A_382)
      | ~ v1_tsep_1(B_381,A_382)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_882])).

tff(c_1575,plain,(
    ! [A_382] :
      ( v1_tsep_1('#skF_3','#skF_4')
      | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_382)
      | ~ m1_pre_topc('#skF_3',A_382)
      | ~ v1_tsep_1('#skF_3',A_382)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1569])).

tff(c_1584,plain,(
    ! [A_382] :
      ( v1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_382)
      | ~ m1_pre_topc('#skF_3',A_382)
      | ~ v1_tsep_1('#skF_3',A_382)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_1575])).

tff(c_2137,plain,(
    ! [A_425] :
      ( ~ m1_pre_topc('#skF_4',A_425)
      | ~ m1_pre_topc('#skF_3',A_425)
      | ~ v1_tsep_1('#skF_3',A_425)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1584])).

tff(c_2140,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1767,c_2137])).

tff(c_2143,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_127,c_659,c_751,c_2140])).

tff(c_2145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.86  
% 4.70/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.86  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.70/1.86  
% 4.70/1.86  %Foreground sorts:
% 4.70/1.86  
% 4.70/1.86  
% 4.70/1.86  %Background operators:
% 4.70/1.86  
% 4.70/1.86  
% 4.70/1.86  %Foreground operators:
% 4.70/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.70/1.86  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.70/1.86  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.70/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.70/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.86  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.70/1.86  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.70/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.70/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.70/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.70/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.70/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.86  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.70/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.70/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.70/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.70/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.70/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.86  
% 4.70/1.89  tff(f_249, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.70/1.89  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.70/1.89  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.70/1.89  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.70/1.89  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.70/1.89  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.70/1.89  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.70/1.89  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.70/1.89  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.70/1.89  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.70/1.89  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.70/1.89  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.70/1.89  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.70/1.89  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 4.70/1.89  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_158, plain, (![B_302, A_303]: (v2_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.70/1.89  tff(c_164, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_158])).
% 4.70/1.89  tff(c_171, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_164])).
% 4.70/1.89  tff(c_114, plain, (![B_299, A_300]: (l1_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.70/1.89  tff(c_120, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_114])).
% 4.70/1.89  tff(c_127, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_120])).
% 4.70/1.89  tff(c_30, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.70/1.89  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.70/1.89  tff(c_91, plain, (![A_297]: (u1_struct_0(A_297)=k2_struct_0(A_297) | ~l1_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.89  tff(c_95, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_91])).
% 4.70/1.89  tff(c_135, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_127, c_95])).
% 4.70/1.89  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_140, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_52])).
% 4.70/1.89  tff(c_413, plain, (![A_319, B_320]: (m1_pre_topc(A_319, g1_pre_topc(u1_struct_0(B_320), u1_pre_topc(B_320))) | ~m1_pre_topc(A_319, B_320) | ~l1_pre_topc(B_320) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.70/1.89  tff(c_430, plain, (![A_319]: (m1_pre_topc(A_319, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_319, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_319))), inference(superposition, [status(thm), theory('equality')], [c_135, c_413])).
% 4.70/1.89  tff(c_464, plain, (![A_321]: (m1_pre_topc(A_321, '#skF_4') | ~m1_pre_topc(A_321, '#skF_3') | ~l1_pre_topc(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_140, c_430])).
% 4.70/1.89  tff(c_475, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_464])).
% 4.70/1.89  tff(c_482, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_475])).
% 4.70/1.89  tff(c_251, plain, (![B_309, A_310]: (m1_pre_topc(B_309, A_310) | ~m1_pre_topc(B_309, g1_pre_topc(u1_struct_0(A_310), u1_pre_topc(A_310))) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.70/1.89  tff(c_257, plain, (![B_309]: (m1_pre_topc(B_309, '#skF_3') | ~m1_pre_topc(B_309, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_251])).
% 4.70/1.89  tff(c_271, plain, (![B_309]: (m1_pre_topc(B_309, '#skF_3') | ~m1_pre_topc(B_309, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_140, c_257])).
% 4.70/1.89  tff(c_175, plain, (![B_304, A_305]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.70/1.89  tff(c_187, plain, (![B_304]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_304, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_175])).
% 4.70/1.89  tff(c_307, plain, (![B_314]: (m1_subset_1(u1_struct_0(B_314), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_314, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_187])).
% 4.70/1.89  tff(c_313, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_135, c_307])).
% 4.70/1.89  tff(c_640, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_313])).
% 4.70/1.89  tff(c_647, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_271, c_640])).
% 4.70/1.89  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_647])).
% 4.70/1.89  tff(c_659, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_313])).
% 4.70/1.89  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_114])).
% 4.70/1.89  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_123])).
% 4.70/1.89  tff(c_139, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_95])).
% 4.70/1.89  tff(c_181, plain, (![B_304]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_304, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_175])).
% 4.70/1.89  tff(c_208, plain, (![B_306]: (m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_306, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_181])).
% 4.70/1.89  tff(c_211, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_208])).
% 4.70/1.89  tff(c_320, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_211])).
% 4.70/1.89  tff(c_323, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_320])).
% 4.70/1.89  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_323])).
% 4.70/1.89  tff(c_329, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_211])).
% 4.70/1.89  tff(c_32, plain, (![B_38, C_40, A_34]: (r1_tarski(u1_struct_0(B_38), u1_struct_0(C_40)) | ~m1_pre_topc(B_38, C_40) | ~m1_pre_topc(C_40, A_34) | ~m1_pre_topc(B_38, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.70/1.89  tff(c_661, plain, (![B_38]: (r1_tarski(u1_struct_0(B_38), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_38, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_659, c_32])).
% 4.70/1.89  tff(c_686, plain, (![B_331]: (r1_tarski(u1_struct_0(B_331), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_331, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_127, c_135, c_661])).
% 4.70/1.89  tff(c_689, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_686])).
% 4.70/1.89  tff(c_742, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_689])).
% 4.70/1.89  tff(c_745, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_271, c_742])).
% 4.70/1.89  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_745])).
% 4.70/1.89  tff(c_751, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_689])).
% 4.70/1.89  tff(c_16, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.70/1.89  tff(c_28, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.70/1.89  tff(c_792, plain, (![B_334, A_335]: (v1_tsep_1(B_334, A_335) | ~v3_pre_topc(u1_struct_0(B_334), A_335) | ~m1_subset_1(u1_struct_0(B_334), k1_zfmisc_1(u1_struct_0(A_335))) | ~m1_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.70/1.89  tff(c_1612, plain, (![B_385, A_386]: (v1_tsep_1(B_385, A_386) | ~v3_pre_topc(u1_struct_0(B_385), A_386) | ~v2_pre_topc(A_386) | ~m1_pre_topc(B_385, A_386) | ~l1_pre_topc(A_386))), inference(resolution, [status(thm)], [c_28, c_792])).
% 4.70/1.89  tff(c_1756, plain, (![A_398]: (v1_tsep_1('#skF_3', A_398) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_398) | ~v2_pre_topc(A_398) | ~m1_pre_topc('#skF_3', A_398) | ~l1_pre_topc(A_398))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1612])).
% 4.70/1.89  tff(c_1763, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1756])).
% 4.70/1.89  tff(c_1767, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_127, c_659, c_1763])).
% 4.70/1.89  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_96, plain, (![A_298]: (u1_struct_0(A_298)=k2_struct_0(A_298) | ~l1_pre_topc(A_298))), inference(resolution, [status(thm)], [c_6, c_91])).
% 4.70/1.89  tff(c_104, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_96])).
% 4.70/1.89  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_109, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56])).
% 4.70/1.89  tff(c_148, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_109])).
% 4.70/1.89  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_146, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_54])).
% 4.70/1.89  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_146])).
% 4.70/1.89  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_149, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_50])).
% 4.70/1.89  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 4.70/1.89  tff(c_141, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_79])).
% 4.70/1.89  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_249])).
% 4.70/1.89  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 4.70/1.89  tff(c_1092, plain, (![D_351, C_350, G_352, A_349, E_348, B_353]: (r1_tmap_1(D_351, B_353, E_348, G_352) | ~r1_tmap_1(C_350, B_353, k3_tmap_1(A_349, B_353, D_351, C_350, E_348), G_352) | ~m1_subset_1(G_352, u1_struct_0(C_350)) | ~m1_subset_1(G_352, u1_struct_0(D_351)) | ~m1_pre_topc(C_350, D_351) | ~v1_tsep_1(C_350, D_351) | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_351), u1_struct_0(B_353)))) | ~v1_funct_2(E_348, u1_struct_0(D_351), u1_struct_0(B_353)) | ~v1_funct_1(E_348) | ~m1_pre_topc(D_351, A_349) | v2_struct_0(D_351) | ~m1_pre_topc(C_350, A_349) | v2_struct_0(C_350) | ~l1_pre_topc(B_353) | ~v2_pre_topc(B_353) | v2_struct_0(B_353) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.70/1.89  tff(c_1094, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_1092])).
% 4.70/1.89  tff(c_1097, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_148, c_104, c_139, c_147, c_104, c_139, c_482, c_149, c_139, c_141, c_135, c_1094])).
% 4.70/1.89  tff(c_1098, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1097])).
% 4.70/1.89  tff(c_167, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_158])).
% 4.70/1.89  tff(c_174, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_167])).
% 4.70/1.89  tff(c_544, plain, (![B_323, C_324, A_325]: (r1_tarski(u1_struct_0(B_323), u1_struct_0(C_324)) | ~m1_pre_topc(B_323, C_324) | ~m1_pre_topc(C_324, A_325) | ~m1_pre_topc(B_323, A_325) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.70/1.89  tff(c_554, plain, (![B_323]: (r1_tarski(u1_struct_0(B_323), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_323, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_329, c_544])).
% 4.70/1.89  tff(c_605, plain, (![B_327]: (r1_tarski(u1_struct_0(B_327), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_327, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_130, c_139, c_554])).
% 4.70/1.89  tff(c_611, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_605])).
% 4.70/1.89  tff(c_621, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_611])).
% 4.70/1.89  tff(c_878, plain, (![B_337, C_338, A_339]: (v1_tsep_1(B_337, C_338) | ~r1_tarski(u1_struct_0(B_337), u1_struct_0(C_338)) | ~m1_pre_topc(C_338, A_339) | v2_struct_0(C_338) | ~m1_pre_topc(B_337, A_339) | ~v1_tsep_1(B_337, A_339) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.70/1.89  tff(c_882, plain, (![B_337, A_339]: (v1_tsep_1(B_337, '#skF_4') | ~r1_tarski(u1_struct_0(B_337), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_339) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_337, A_339) | ~v1_tsep_1(B_337, A_339) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(superposition, [status(thm), theory('equality')], [c_139, c_878])).
% 4.70/1.89  tff(c_1569, plain, (![B_381, A_382]: (v1_tsep_1(B_381, '#skF_4') | ~r1_tarski(u1_struct_0(B_381), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_382) | ~m1_pre_topc(B_381, A_382) | ~v1_tsep_1(B_381, A_382) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(negUnitSimplification, [status(thm)], [c_62, c_882])).
% 4.70/1.89  tff(c_1575, plain, (![A_382]: (v1_tsep_1('#skF_3', '#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_382) | ~m1_pre_topc('#skF_3', A_382) | ~v1_tsep_1('#skF_3', A_382) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1569])).
% 4.70/1.89  tff(c_1584, plain, (![A_382]: (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_382) | ~m1_pre_topc('#skF_3', A_382) | ~v1_tsep_1('#skF_3', A_382) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_1575])).
% 4.70/1.89  tff(c_2137, plain, (![A_425]: (~m1_pre_topc('#skF_4', A_425) | ~m1_pre_topc('#skF_3', A_425) | ~v1_tsep_1('#skF_3', A_425) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(negUnitSimplification, [status(thm)], [c_1098, c_1584])).
% 4.70/1.89  tff(c_2140, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1767, c_2137])).
% 4.70/1.89  tff(c_2143, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_127, c_659, c_751, c_2140])).
% 4.70/1.89  tff(c_2145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2143])).
% 4.70/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.89  
% 4.70/1.89  Inference rules
% 4.70/1.89  ----------------------
% 4.70/1.89  #Ref     : 0
% 4.70/1.89  #Sup     : 431
% 4.70/1.89  #Fact    : 0
% 4.70/1.89  #Define  : 0
% 4.70/1.89  #Split   : 17
% 4.70/1.89  #Chain   : 0
% 4.70/1.89  #Close   : 0
% 4.70/1.89  
% 4.70/1.89  Ordering : KBO
% 4.70/1.89  
% 4.70/1.89  Simplification rules
% 4.70/1.89  ----------------------
% 4.70/1.89  #Subsume      : 113
% 4.70/1.89  #Demod        : 547
% 4.70/1.89  #Tautology    : 117
% 4.70/1.89  #SimpNegUnit  : 22
% 4.70/1.89  #BackRed      : 6
% 4.70/1.89  
% 4.70/1.89  #Partial instantiations: 0
% 4.70/1.89  #Strategies tried      : 1
% 4.70/1.89  
% 4.70/1.89  Timing (in seconds)
% 4.70/1.89  ----------------------
% 4.70/1.89  Preprocessing        : 0.39
% 4.70/1.89  Parsing              : 0.20
% 4.70/1.89  CNF conversion       : 0.05
% 4.70/1.89  Main loop            : 0.65
% 4.70/1.89  Inferencing          : 0.20
% 4.70/1.89  Reduction            : 0.25
% 4.70/1.89  Demodulation         : 0.18
% 4.70/1.89  BG Simplification    : 0.03
% 4.70/1.89  Subsumption          : 0.13
% 4.70/1.89  Abstraction          : 0.02
% 4.70/1.89  MUC search           : 0.00
% 4.70/1.89  Cooper               : 0.00
% 4.70/1.89  Total                : 1.09
% 4.70/1.89  Index Insertion      : 0.00
% 4.70/1.89  Index Deletion       : 0.00
% 4.70/1.89  Index Matching       : 0.00
% 4.70/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
