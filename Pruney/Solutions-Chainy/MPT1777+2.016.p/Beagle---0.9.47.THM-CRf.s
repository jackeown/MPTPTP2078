%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:34 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  126 (1788 expanded)
%              Number of leaves         :   44 ( 637 expanded)
%              Depth                    :   17
%              Number of atoms          :  272 (8454 expanded)
%              Number of equality atoms :   38 (1089 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_231,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_182,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_117,plain,(
    ! [B_291,A_292] :
      ( l1_pre_topc(B_291)
      | ~ m1_pre_topc(B_291,A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_123])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_97])).

tff(c_98,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_142,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56])).

tff(c_180,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126])).

tff(c_36,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_181,plain,(
    ! [B_295,A_296] :
      ( v2_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_190,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_181])).

tff(c_197,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_190])).

tff(c_141,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_148,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_198,plain,(
    ! [A_297] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_297),u1_pre_topc(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_201,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_198])).

tff(c_212,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_133,c_148,c_201])).

tff(c_219,plain,(
    ! [A_298] :
      ( g1_pre_topc(u1_struct_0(A_298),u1_pre_topc(A_298)) = A_298
      | ~ v1_pre_topc(A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_219])).

tff(c_246,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_234])).

tff(c_253,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_246])).

tff(c_159,plain,(
    ! [A_294] :
      ( m1_subset_1(u1_pre_topc(A_294),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_294))))
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_173,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_162])).

tff(c_429,plain,(
    ! [D_310,B_311,C_312,A_313] :
      ( D_310 = B_311
      | g1_pre_topc(C_312,D_310) != g1_pre_topc(A_313,B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k1_zfmisc_1(A_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_441,plain,(
    ! [D_310,C_312] :
      ( u1_pre_topc('#skF_3') = D_310
      | g1_pre_topc(C_312,D_310) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_429])).

tff(c_446,plain,(
    ! [D_314,C_315] :
      ( u1_pre_topc('#skF_3') = D_314
      | g1_pre_topc(C_315,D_314) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_441])).

tff(c_456,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_446])).

tff(c_461,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_148])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_159])).

tff(c_175,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_165])).

tff(c_528,plain,(
    ! [C_319,A_320,D_321,B_322] :
      ( C_319 = A_320
      | g1_pre_topc(C_319,D_321) != g1_pre_topc(A_320,B_322)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(k1_zfmisc_1(A_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_536,plain,(
    ! [C_319,D_321] :
      ( k2_struct_0('#skF_4') = C_319
      | g1_pre_topc(C_319,D_321) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_528])).

tff(c_545,plain,(
    ! [C_323,D_324] :
      ( k2_struct_0('#skF_4') = C_323
      | g1_pre_topc(C_323,D_324) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_536])).

tff(c_555,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_545])).

tff(c_563,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_141])).

tff(c_820,plain,(
    ! [A_331,B_332] :
      ( m1_pre_topc(A_331,g1_pre_topc(u1_struct_0(B_332),u1_pre_topc(B_332)))
      | ~ m1_pre_topc(A_331,B_332)
      | ~ l1_pre_topc(B_332)
      | ~ l1_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_841,plain,(
    ! [A_331] :
      ( m1_pre_topc(A_331,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_331,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_820])).

tff(c_871,plain,(
    ! [A_333] :
      ( m1_pre_topc(A_333,'#skF_4')
      | ~ m1_pre_topc(A_333,'#skF_3')
      | ~ l1_pre_topc(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_253,c_563,c_841])).

tff(c_885,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_871])).

tff(c_895,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_885])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_143,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1270,plain,(
    ! [B_349,G_350,A_347,D_351,E_348,C_352] :
      ( r1_tmap_1(D_351,B_349,E_348,G_350)
      | ~ r1_tmap_1(C_352,B_349,k3_tmap_1(A_347,B_349,D_351,C_352,E_348),G_350)
      | ~ m1_subset_1(G_350,u1_struct_0(C_352))
      | ~ m1_subset_1(G_350,u1_struct_0(D_351))
      | ~ m1_pre_topc(C_352,D_351)
      | ~ v1_tsep_1(C_352,D_351)
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_351),u1_struct_0(B_349))))
      | ~ v1_funct_2(E_348,u1_struct_0(D_351),u1_struct_0(B_349))
      | ~ v1_funct_1(E_348)
      | ~ m1_pre_topc(D_351,A_347)
      | v2_struct_0(D_351)
      | ~ m1_pre_topc(C_352,A_347)
      | v2_struct_0(C_352)
      | ~ l1_pre_topc(B_349)
      | ~ v2_pre_topc(B_349)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1272,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1270])).

tff(c_1275,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_142,c_105,c_137,c_180,c_105,c_137,c_895,c_143,c_137,c_143,c_563,c_1272])).

tff(c_1276,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1275])).

tff(c_187,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_194,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187])).

tff(c_26,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_949,plain,(
    ! [B_334,A_335] :
      ( v1_tsep_1(B_334,A_335)
      | ~ v3_pre_topc(u1_struct_0(B_334),A_335)
      | ~ m1_subset_1(u1_struct_0(B_334),k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ m1_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1441,plain,(
    ! [B_368,A_369] :
      ( v1_tsep_1(B_368,A_369)
      | ~ v3_pre_topc(u1_struct_0(B_368),A_369)
      | ~ v2_pre_topc(A_369)
      | ~ m1_pre_topc(B_368,A_369)
      | ~ l1_pre_topc(A_369) ) ),
    inference(resolution,[status(thm)],[c_34,c_949])).

tff(c_1607,plain,(
    ! [A_391] :
      ( v1_tsep_1('#skF_3',A_391)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_391)
      | ~ v2_pre_topc(A_391)
      | ~ m1_pre_topc('#skF_3',A_391)
      | ~ l1_pre_topc(A_391) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_1441])).

tff(c_1620,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1607])).

tff(c_1628,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_130,c_895,c_1620])).

tff(c_1630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1276,c_1628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.88  
% 4.62/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.88  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.62/1.88  
% 4.62/1.88  %Foreground sorts:
% 4.62/1.88  
% 4.62/1.88  
% 4.62/1.88  %Background operators:
% 4.62/1.88  
% 4.62/1.88  
% 4.62/1.88  %Foreground operators:
% 4.62/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.62/1.88  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.88  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.62/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.88  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.62/1.88  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.62/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.88  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.62/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.88  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.62/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.62/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.62/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.88  
% 4.96/1.90  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.96/1.90  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.96/1.90  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.96/1.90  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.96/1.90  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.96/1.90  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.96/1.90  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 4.96/1.90  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.96/1.90  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.96/1.90  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.96/1.90  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.96/1.90  tff(f_182, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.96/1.90  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.96/1.90  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.96/1.90  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.96/1.90  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_117, plain, (![B_291, A_292]: (l1_pre_topc(B_291) | ~m1_pre_topc(B_291, A_292) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.96/1.90  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117])).
% 4.96/1.90  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_123])).
% 4.96/1.90  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.96/1.90  tff(c_93, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.96/1.90  tff(c_97, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.96/1.90  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_97])).
% 4.96/1.90  tff(c_98, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.96/1.90  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 4.96/1.90  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 4.96/1.90  tff(c_142, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 4.96/1.90  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56])).
% 4.96/1.90  tff(c_180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 4.96/1.90  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 4.96/1.90  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126])).
% 4.96/1.90  tff(c_36, plain, (![A_32]: (m1_pre_topc(A_32, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.96/1.90  tff(c_181, plain, (![B_295, A_296]: (v2_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.96/1.90  tff(c_190, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_181])).
% 4.96/1.90  tff(c_197, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_190])).
% 4.96/1.90  tff(c_141, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 4.96/1.90  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_148, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 4.96/1.90  tff(c_198, plain, (![A_297]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_297), u1_pre_topc(A_297))) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.96/1.90  tff(c_201, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_198])).
% 4.96/1.90  tff(c_212, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_133, c_148, c_201])).
% 4.96/1.90  tff(c_219, plain, (![A_298]: (g1_pre_topc(u1_struct_0(A_298), u1_pre_topc(A_298))=A_298 | ~v1_pre_topc(A_298) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/1.90  tff(c_234, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_219])).
% 4.96/1.90  tff(c_246, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_234])).
% 4.96/1.90  tff(c_253, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_246])).
% 4.96/1.90  tff(c_159, plain, (![A_294]: (m1_subset_1(u1_pre_topc(A_294), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_294)))) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.96/1.90  tff(c_162, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 4.96/1.90  tff(c_173, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_162])).
% 4.96/1.90  tff(c_429, plain, (![D_310, B_311, C_312, A_313]: (D_310=B_311 | g1_pre_topc(C_312, D_310)!=g1_pre_topc(A_313, B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(k1_zfmisc_1(A_313))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.96/1.90  tff(c_441, plain, (![D_310, C_312]: (u1_pre_topc('#skF_3')=D_310 | g1_pre_topc(C_312, D_310)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_429])).
% 4.96/1.90  tff(c_446, plain, (![D_314, C_315]: (u1_pre_topc('#skF_3')=D_314 | g1_pre_topc(C_315, D_314)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_441])).
% 4.96/1.90  tff(c_456, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_253, c_446])).
% 4.96/1.90  tff(c_461, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_148])).
% 4.96/1.90  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_159])).
% 4.96/1.90  tff(c_175, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_165])).
% 4.96/1.90  tff(c_528, plain, (![C_319, A_320, D_321, B_322]: (C_319=A_320 | g1_pre_topc(C_319, D_321)!=g1_pre_topc(A_320, B_322) | ~m1_subset_1(B_322, k1_zfmisc_1(k1_zfmisc_1(A_320))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.96/1.90  tff(c_536, plain, (![C_319, D_321]: (k2_struct_0('#skF_4')=C_319 | g1_pre_topc(C_319, D_321)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_253, c_528])).
% 4.96/1.90  tff(c_545, plain, (![C_323, D_324]: (k2_struct_0('#skF_4')=C_323 | g1_pre_topc(C_323, D_324)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_536])).
% 4.96/1.90  tff(c_555, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_461, c_545])).
% 4.96/1.90  tff(c_563, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_141])).
% 4.96/1.90  tff(c_820, plain, (![A_331, B_332]: (m1_pre_topc(A_331, g1_pre_topc(u1_struct_0(B_332), u1_pre_topc(B_332))) | ~m1_pre_topc(A_331, B_332) | ~l1_pre_topc(B_332) | ~l1_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.96/1.90  tff(c_841, plain, (![A_331]: (m1_pre_topc(A_331, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_331, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_331))), inference(superposition, [status(thm), theory('equality')], [c_456, c_820])).
% 4.96/1.90  tff(c_871, plain, (![A_333]: (m1_pre_topc(A_333, '#skF_4') | ~m1_pre_topc(A_333, '#skF_3') | ~l1_pre_topc(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_253, c_563, c_841])).
% 4.96/1.90  tff(c_885, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_871])).
% 4.96/1.90  tff(c_895, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_885])).
% 4.96/1.90  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_143, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_52])).
% 4.96/1.90  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.96/1.90  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.96/1.90  tff(c_1270, plain, (![B_349, G_350, A_347, D_351, E_348, C_352]: (r1_tmap_1(D_351, B_349, E_348, G_350) | ~r1_tmap_1(C_352, B_349, k3_tmap_1(A_347, B_349, D_351, C_352, E_348), G_350) | ~m1_subset_1(G_350, u1_struct_0(C_352)) | ~m1_subset_1(G_350, u1_struct_0(D_351)) | ~m1_pre_topc(C_352, D_351) | ~v1_tsep_1(C_352, D_351) | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_351), u1_struct_0(B_349)))) | ~v1_funct_2(E_348, u1_struct_0(D_351), u1_struct_0(B_349)) | ~v1_funct_1(E_348) | ~m1_pre_topc(D_351, A_347) | v2_struct_0(D_351) | ~m1_pre_topc(C_352, A_347) | v2_struct_0(C_352) | ~l1_pre_topc(B_349) | ~v2_pre_topc(B_349) | v2_struct_0(B_349) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.96/1.90  tff(c_1272, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1270])).
% 4.96/1.90  tff(c_1275, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_142, c_105, c_137, c_180, c_105, c_137, c_895, c_143, c_137, c_143, c_563, c_1272])).
% 4.96/1.90  tff(c_1276, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1275])).
% 4.96/1.90  tff(c_187, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_181])).
% 4.96/1.90  tff(c_194, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187])).
% 4.96/1.90  tff(c_26, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.96/1.90  tff(c_34, plain, (![B_31, A_29]: (m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.96/1.90  tff(c_949, plain, (![B_334, A_335]: (v1_tsep_1(B_334, A_335) | ~v3_pre_topc(u1_struct_0(B_334), A_335) | ~m1_subset_1(u1_struct_0(B_334), k1_zfmisc_1(u1_struct_0(A_335))) | ~m1_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/1.90  tff(c_1441, plain, (![B_368, A_369]: (v1_tsep_1(B_368, A_369) | ~v3_pre_topc(u1_struct_0(B_368), A_369) | ~v2_pre_topc(A_369) | ~m1_pre_topc(B_368, A_369) | ~l1_pre_topc(A_369))), inference(resolution, [status(thm)], [c_34, c_949])).
% 4.96/1.90  tff(c_1607, plain, (![A_391]: (v1_tsep_1('#skF_3', A_391) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_391) | ~v2_pre_topc(A_391) | ~m1_pre_topc('#skF_3', A_391) | ~l1_pre_topc(A_391))), inference(superposition, [status(thm), theory('equality')], [c_563, c_1441])).
% 4.96/1.90  tff(c_1620, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1607])).
% 4.96/1.90  tff(c_1628, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_130, c_895, c_1620])).
% 4.96/1.90  tff(c_1630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1276, c_1628])).
% 4.96/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.90  
% 4.96/1.90  Inference rules
% 4.96/1.90  ----------------------
% 4.96/1.90  #Ref     : 3
% 4.96/1.90  #Sup     : 316
% 4.96/1.90  #Fact    : 0
% 4.96/1.90  #Define  : 0
% 4.96/1.90  #Split   : 16
% 4.96/1.90  #Chain   : 0
% 4.96/1.90  #Close   : 0
% 4.96/1.90  
% 4.96/1.90  Ordering : KBO
% 4.96/1.90  
% 4.96/1.90  Simplification rules
% 4.96/1.90  ----------------------
% 4.96/1.90  #Subsume      : 53
% 4.96/1.90  #Demod        : 440
% 4.96/1.90  #Tautology    : 125
% 4.96/1.90  #SimpNegUnit  : 16
% 4.96/1.90  #BackRed      : 16
% 4.96/1.90  
% 4.96/1.90  #Partial instantiations: 0
% 4.96/1.90  #Strategies tried      : 1
% 4.96/1.90  
% 4.96/1.90  Timing (in seconds)
% 4.96/1.90  ----------------------
% 4.96/1.91  Preprocessing        : 0.46
% 4.96/1.91  Parsing              : 0.23
% 4.96/1.91  CNF conversion       : 0.05
% 4.96/1.91  Main loop            : 0.57
% 4.96/1.91  Inferencing          : 0.18
% 4.96/1.91  Reduction            : 0.20
% 4.96/1.91  Demodulation         : 0.15
% 4.96/1.91  BG Simplification    : 0.03
% 4.96/1.91  Subsumption          : 0.11
% 4.96/1.91  Abstraction          : 0.02
% 4.96/1.91  MUC search           : 0.00
% 4.96/1.91  Cooper               : 0.00
% 4.96/1.91  Total                : 1.09
% 4.96/1.91  Index Insertion      : 0.00
% 4.96/1.91  Index Deletion       : 0.00
% 4.96/1.91  Index Matching       : 0.00
% 4.96/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
