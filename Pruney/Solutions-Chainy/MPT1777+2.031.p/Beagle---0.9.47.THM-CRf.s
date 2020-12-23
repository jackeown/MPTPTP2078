%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 24.68s
% Output     : CNFRefutation 24.93s
% Verified   : 
% Statistics : Number of formulae       :  177 (2698 expanded)
%              Number of leaves         :   48 ( 945 expanded)
%              Depth                    :   26
%              Number of atoms          :  511 (12814 expanded)
%              Number of equality atoms :   46 (1470 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_315,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_194,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_198,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_137,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_212,axiom,(
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

tff(f_169,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_187,axiom,(
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

tff(f_254,axiom,(
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

tff(c_62,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_94,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_80,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_142,plain,(
    ! [B_291,A_292] :
      ( l1_pre_topc(B_291)
      | ~ m1_pre_topc(B_291,A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_142])).

tff(c_158,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_151])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_166,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_158,c_128])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_180,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_70])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_96,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_84,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_148,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_142])).

tff(c_155,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_148])).

tff(c_162,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_128])).

tff(c_215,plain,(
    ! [B_298,A_299] :
      ( m1_subset_1(u1_struct_0(B_298),k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_221,plain,(
    ! [B_298] :
      ( m1_subset_1(u1_struct_0(B_298),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_298,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_215])).

tff(c_248,plain,(
    ! [B_300] :
      ( m1_subset_1(u1_struct_0(B_300),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_300,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_221])).

tff(c_254,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_248])).

tff(c_377,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_50,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_72,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_173,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_72])).

tff(c_516,plain,(
    ! [A_316,B_317] :
      ( m1_pre_topc(A_316,g1_pre_topc(u1_struct_0(B_317),u1_pre_topc(B_317)))
      | ~ m1_pre_topc(A_316,B_317)
      | ~ l1_pre_topc(B_317)
      | ~ l1_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_537,plain,(
    ! [A_316] :
      ( m1_pre_topc(A_316,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_316,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_516])).

tff(c_565,plain,(
    ! [A_318] :
      ( m1_pre_topc(A_318,'#skF_4')
      | ~ m1_pre_topc(A_318,'#skF_3')
      | ~ l1_pre_topc(A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_173,c_537])).

tff(c_579,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_565])).

tff(c_590,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_579])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_590])).

tff(c_594,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_262,plain,(
    ! [B_301,A_302] :
      ( m1_pre_topc(B_301,A_302)
      | ~ m1_pre_topc(B_301,g1_pre_topc(u1_struct_0(A_302),u1_pre_topc(A_302)))
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_268,plain,(
    ! [B_301] :
      ( m1_pre_topc(B_301,'#skF_3')
      | ~ m1_pre_topc(B_301,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_262])).

tff(c_282,plain,(
    ! [B_301] :
      ( m1_pre_topc(B_301,'#skF_3')
      | ~ m1_pre_topc(B_301,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_173,c_268])).

tff(c_227,plain,(
    ! [B_298] :
      ( m1_subset_1(u1_struct_0(B_298),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_298,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_215])).

tff(c_363,plain,(
    ! [B_311] :
      ( m1_subset_1(u1_struct_0(B_311),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_311,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_227])).

tff(c_366,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_363])).

tff(c_695,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_699,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_695])).

tff(c_742,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_699])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_742])).

tff(c_748,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_640,plain,(
    ! [A_320,B_321] :
      ( m1_pre_topc(A_320,g1_pre_topc(u1_struct_0(B_321),u1_pre_topc(B_321)))
      | ~ m1_pre_topc(A_320,B_321)
      | ~ l1_pre_topc(B_321)
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_661,plain,(
    ! [A_320] :
      ( m1_pre_topc(A_320,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_320,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_640])).

tff(c_678,plain,(
    ! [A_320] :
      ( m1_pre_topc(A_320,'#skF_4')
      | ~ m1_pre_topc(A_320,'#skF_3')
      | ~ l1_pre_topc(A_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_173,c_661])).

tff(c_751,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_748,c_678])).

tff(c_762,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_751])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_88,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_129,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_137,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_129])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_167,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_76])).

tff(c_185,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_167])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_172,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_74])).

tff(c_179,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_172])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_198,plain,(
    ! [B_296,A_297] :
      ( v2_pre_topc(B_296)
      | ~ m1_pre_topc(B_296,A_297)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_198])).

tff(c_214,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_207])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_90,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_2355,plain,(
    ! [A_395,B_396,C_397,D_398] :
      ( k2_partfun1(u1_struct_0(A_395),u1_struct_0(B_396),C_397,u1_struct_0(D_398)) = k2_tmap_1(A_395,B_396,C_397,D_398)
      | ~ m1_pre_topc(D_398,A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_396))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0(B_396))
      | ~ v1_funct_1(C_397)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | v2_struct_0(B_396)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2367,plain,(
    ! [A_395,C_397,D_398] :
      ( k2_partfun1(u1_struct_0(A_395),u1_struct_0('#skF_2'),C_397,u1_struct_0(D_398)) = k2_tmap_1(A_395,'#skF_2',C_397,D_398)
      | ~ m1_pre_topc(D_398,A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_397)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_2355])).

tff(c_2391,plain,(
    ! [A_395,C_397,D_398] :
      ( k2_partfun1(u1_struct_0(A_395),k2_struct_0('#skF_2'),C_397,u1_struct_0(D_398)) = k2_tmap_1(A_395,'#skF_2',C_397,D_398)
      | ~ m1_pre_topc(D_398,A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_397)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_137,c_137,c_2367])).

tff(c_5390,plain,(
    ! [A_560,C_561,D_562] :
      ( k2_partfun1(u1_struct_0(A_560),k2_struct_0('#skF_2'),C_561,u1_struct_0(D_562)) = k2_tmap_1(A_560,'#skF_2',C_561,D_562)
      | ~ m1_pre_topc(D_562,A_560)
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_560),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_561,u1_struct_0(A_560),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2391])).

tff(c_5394,plain,(
    ! [C_561,D_562] :
      ( k2_partfun1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_561,u1_struct_0(D_562)) = k2_tmap_1('#skF_4','#skF_2',C_561,D_562)
      | ~ m1_pre_topc(D_562,'#skF_4')
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_561,u1_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_561)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_5390])).

tff(c_5406,plain,(
    ! [C_561,D_562] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_561,u1_struct_0(D_562)) = k2_tmap_1('#skF_4','#skF_2',C_561,D_562)
      | ~ m1_pre_topc(D_562,'#skF_4')
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_561,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_561)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_158,c_166,c_166,c_5394])).

tff(c_5855,plain,(
    ! [C_574,D_575] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_574,u1_struct_0(D_575)) = k2_tmap_1('#skF_4','#skF_2',C_574,D_575)
      | ~ m1_pre_topc(D_575,'#skF_4')
      | ~ m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_574,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5406])).

tff(c_5857,plain,(
    ! [D_575] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_575)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_575)
      | ~ m1_pre_topc(D_575,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_179,c_5855])).

tff(c_5865,plain,(
    ! [D_576] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_576)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_576)
      | ~ m1_pre_topc(D_576,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_185,c_5857])).

tff(c_5877,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_5865])).

tff(c_5889,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_5877])).

tff(c_204,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_198])).

tff(c_211,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_204])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_862,plain,(
    ! [B_328,C_329,A_330] :
      ( m1_pre_topc(B_328,C_329)
      | ~ r1_tarski(u1_struct_0(B_328),u1_struct_0(C_329))
      | ~ m1_pre_topc(C_329,A_330)
      | ~ m1_pre_topc(B_328,A_330)
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_884,plain,(
    ! [B_331,A_332] :
      ( m1_pre_topc(B_331,B_331)
      | ~ m1_pre_topc(B_331,A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332) ) ),
    inference(resolution,[status(thm)],[c_6,c_862])).

tff(c_900,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_884])).

tff(c_920,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_900])).

tff(c_1011,plain,(
    ! [B_338,C_339,A_340] :
      ( r1_tarski(u1_struct_0(B_338),u1_struct_0(C_339))
      | ~ m1_pre_topc(B_338,C_339)
      | ~ m1_pre_topc(C_339,A_340)
      | ~ m1_pre_topc(B_338,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1013,plain,(
    ! [B_338] :
      ( r1_tarski(u1_struct_0(B_338),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_338,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_920,c_1011])).

tff(c_1057,plain,(
    ! [B_341] :
      ( r1_tarski(u1_struct_0(B_341),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_341,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_155,c_162,c_1013])).

tff(c_1062,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1057])).

tff(c_1074,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_1062])).

tff(c_1017,plain,(
    ! [B_338] :
      ( r1_tarski(u1_struct_0(B_338),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_338,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_762,c_1011])).

tff(c_1108,plain,(
    ! [B_344] :
      ( r1_tarski(u1_struct_0(B_344),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_344,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_158,c_166,c_1017])).

tff(c_1116,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1108])).

tff(c_1127,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_1116])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1129,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1127,c_2])).

tff(c_1132,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_1129])).

tff(c_1145,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_162])).

tff(c_2611,plain,(
    ! [B_413,D_410,C_414,E_411,A_412] :
      ( k3_tmap_1(A_412,B_413,C_414,D_410,E_411) = k2_partfun1(u1_struct_0(C_414),u1_struct_0(B_413),E_411,u1_struct_0(D_410))
      | ~ m1_pre_topc(D_410,C_414)
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_414),u1_struct_0(B_413))))
      | ~ v1_funct_2(E_411,u1_struct_0(C_414),u1_struct_0(B_413))
      | ~ v1_funct_1(E_411)
      | ~ m1_pre_topc(D_410,A_412)
      | ~ m1_pre_topc(C_414,A_412)
      | ~ l1_pre_topc(B_413)
      | ~ v2_pre_topc(B_413)
      | v2_struct_0(B_413)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2617,plain,(
    ! [A_412,B_413,D_410,E_411] :
      ( k3_tmap_1(A_412,B_413,'#skF_4',D_410,E_411) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_413),E_411,u1_struct_0(D_410))
      | ~ m1_pre_topc(D_410,'#skF_4')
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_413))))
      | ~ v1_funct_2(E_411,u1_struct_0('#skF_4'),u1_struct_0(B_413))
      | ~ v1_funct_1(E_411)
      | ~ m1_pre_topc(D_410,A_412)
      | ~ m1_pre_topc('#skF_4',A_412)
      | ~ l1_pre_topc(B_413)
      | ~ v2_pre_topc(B_413)
      | v2_struct_0(B_413)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2611])).

tff(c_38559,plain,(
    ! [A_1202,B_1203,D_1204,E_1205] :
      ( k3_tmap_1(A_1202,B_1203,'#skF_4',D_1204,E_1205) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_1203),E_1205,u1_struct_0(D_1204))
      | ~ m1_pre_topc(D_1204,'#skF_4')
      | ~ m1_subset_1(E_1205,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_1203))))
      | ~ v1_funct_2(E_1205,k2_struct_0('#skF_4'),u1_struct_0(B_1203))
      | ~ v1_funct_1(E_1205)
      | ~ m1_pre_topc(D_1204,A_1202)
      | ~ m1_pre_topc('#skF_4',A_1202)
      | ~ l1_pre_topc(B_1203)
      | ~ v2_pre_topc(B_1203)
      | v2_struct_0(B_1203)
      | ~ l1_pre_topc(A_1202)
      | ~ v2_pre_topc(A_1202)
      | v2_struct_0(A_1202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_2617])).

tff(c_38565,plain,(
    ! [A_1202,D_1204,E_1205] :
      ( k3_tmap_1(A_1202,'#skF_2','#skF_4',D_1204,E_1205) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_1205,u1_struct_0(D_1204))
      | ~ m1_pre_topc(D_1204,'#skF_4')
      | ~ m1_subset_1(E_1205,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1205,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1205)
      | ~ m1_pre_topc(D_1204,A_1202)
      | ~ m1_pre_topc('#skF_4',A_1202)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1202)
      | ~ v2_pre_topc(A_1202)
      | v2_struct_0(A_1202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_38559])).

tff(c_38578,plain,(
    ! [A_1202,D_1204,E_1205] :
      ( k3_tmap_1(A_1202,'#skF_2','#skF_4',D_1204,E_1205) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1205,u1_struct_0(D_1204))
      | ~ m1_pre_topc(D_1204,'#skF_4')
      | ~ m1_subset_1(E_1205,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1205,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1205)
      | ~ m1_pre_topc(D_1204,A_1202)
      | ~ m1_pre_topc('#skF_4',A_1202)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1202)
      | ~ v2_pre_topc(A_1202)
      | v2_struct_0(A_1202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_137,c_137,c_38565])).

tff(c_58752,plain,(
    ! [A_1613,D_1614,E_1615] :
      ( k3_tmap_1(A_1613,'#skF_2','#skF_4',D_1614,E_1615) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1615,u1_struct_0(D_1614))
      | ~ m1_pre_topc(D_1614,'#skF_4')
      | ~ m1_subset_1(E_1615,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1615,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1615)
      | ~ m1_pre_topc(D_1614,A_1613)
      | ~ m1_pre_topc('#skF_4',A_1613)
      | ~ l1_pre_topc(A_1613)
      | ~ v2_pre_topc(A_1613)
      | v2_struct_0(A_1613) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_38578])).

tff(c_58754,plain,(
    ! [A_1613,D_1614] :
      ( k3_tmap_1(A_1613,'#skF_2','#skF_4',D_1614,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1614))
      | ~ m1_pre_topc(D_1614,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_1614,A_1613)
      | ~ m1_pre_topc('#skF_4',A_1613)
      | ~ l1_pre_topc(A_1613)
      | ~ v2_pre_topc(A_1613)
      | v2_struct_0(A_1613) ) ),
    inference(resolution,[status(thm)],[c_179,c_58752])).

tff(c_58762,plain,(
    ! [A_1616,D_1617] :
      ( k3_tmap_1(A_1616,'#skF_2','#skF_4',D_1617,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1617))
      | ~ m1_pre_topc(D_1617,'#skF_4')
      | ~ m1_pre_topc(D_1617,A_1616)
      | ~ m1_pre_topc('#skF_4',A_1616)
      | ~ l1_pre_topc(A_1616)
      | ~ v2_pre_topc(A_1616)
      | v2_struct_0(A_1616) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_185,c_58754])).

tff(c_58868,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_58762])).

tff(c_58997,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_594,c_5889,c_1145,c_58868])).

tff(c_58998,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_58997])).

tff(c_66,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_64,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_100,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64])).

tff(c_59064,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58998,c_100])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_36,plain,(
    ! [A_29] :
      ( v3_pre_topc(k2_struct_0(A_29),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    ! [B_85,A_83] :
      ( m1_subset_1(u1_struct_0(B_85),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_pre_topc(B_85,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1320,plain,(
    ! [B_353,A_354] :
      ( v1_tsep_1(B_353,A_354)
      | ~ v3_pre_topc(u1_struct_0(B_353),A_354)
      | ~ m1_subset_1(u1_struct_0(B_353),k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_pre_topc(B_353,A_354)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2564,plain,(
    ! [B_407,A_408] :
      ( v1_tsep_1(B_407,A_408)
      | ~ v3_pre_topc(u1_struct_0(B_407),A_408)
      | ~ v2_pre_topc(A_408)
      | ~ m1_pre_topc(B_407,A_408)
      | ~ l1_pre_topc(A_408) ) ),
    inference(resolution,[status(thm)],[c_48,c_1320])).

tff(c_3872,plain,(
    ! [A_492] :
      ( v1_tsep_1('#skF_3',A_492)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_492)
      | ~ v2_pre_topc(A_492)
      | ~ m1_pre_topc('#skF_3',A_492)
      | ~ l1_pre_topc(A_492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_2564])).

tff(c_3889,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3872])).

tff(c_3900,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_158,c_594,c_3889])).

tff(c_5874,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_5865])).

tff(c_5887,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_5874])).

tff(c_5894,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5889,c_5887])).

tff(c_56,plain,(
    ! [B_126,D_150,F_156,C_142,A_94] :
      ( r1_tmap_1(B_126,A_94,C_142,F_156)
      | ~ r1_tmap_1(D_150,A_94,k2_tmap_1(B_126,A_94,C_142,D_150),F_156)
      | ~ m1_subset_1(F_156,u1_struct_0(D_150))
      | ~ m1_subset_1(F_156,u1_struct_0(B_126))
      | ~ m1_pre_topc(D_150,B_126)
      | ~ v1_tsep_1(D_150,B_126)
      | v2_struct_0(D_150)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_126),u1_struct_0(A_94))))
      | ~ v1_funct_2(C_142,u1_struct_0(B_126),u1_struct_0(A_94))
      | ~ v1_funct_1(C_142)
      | ~ l1_pre_topc(B_126)
      | ~ v2_pre_topc(B_126)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_5897,plain,(
    ! [F_156] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_156)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_156)
      | ~ m1_subset_1(F_156,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_156,u1_struct_0('#skF_4'))
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
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5894,c_56])).

tff(c_5901,plain,(
    ! [F_156] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_156)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_156)
      | ~ m1_subset_1(F_156,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_214,c_158,c_78,c_185,c_137,c_166,c_179,c_137,c_166,c_3900,c_594,c_166,c_1145,c_5897])).

tff(c_5902,plain,(
    ! [F_156] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_156)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_156)
      | ~ m1_subset_1(F_156,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_82,c_86,c_5901])).

tff(c_59074,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59064,c_5902])).

tff(c_59080,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_59074])).

tff(c_59082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_59080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:41:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.68/15.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.68/15.90  
% 24.68/15.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.68/15.91  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 24.68/15.91  
% 24.68/15.91  %Foreground sorts:
% 24.68/15.91  
% 24.68/15.91  
% 24.68/15.91  %Background operators:
% 24.68/15.91  
% 24.68/15.91  
% 24.68/15.91  %Foreground operators:
% 24.68/15.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.68/15.91  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 24.68/15.91  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 24.68/15.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.68/15.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 24.68/15.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.68/15.91  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 24.68/15.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 24.68/15.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.68/15.91  tff('#skF_7', type, '#skF_7': $i).
% 24.68/15.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.68/15.91  tff('#skF_5', type, '#skF_5': $i).
% 24.68/15.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.68/15.91  tff('#skF_6', type, '#skF_6': $i).
% 24.68/15.91  tff('#skF_2', type, '#skF_2': $i).
% 24.68/15.91  tff('#skF_3', type, '#skF_3': $i).
% 24.68/15.91  tff('#skF_1', type, '#skF_1': $i).
% 24.68/15.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.68/15.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 24.68/15.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.68/15.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.68/15.91  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 24.68/15.91  tff('#skF_4', type, '#skF_4': $i).
% 24.68/15.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.68/15.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 24.68/15.91  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 24.68/15.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.68/15.91  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 24.68/15.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.68/15.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 24.68/15.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 24.68/15.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.68/15.91  
% 24.93/15.93  tff(f_315, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 24.93/15.93  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 24.93/15.93  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 24.93/15.93  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 24.93/15.93  tff(f_194, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 24.93/15.93  tff(f_198, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 24.93/15.93  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 24.93/15.93  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 24.93/15.93  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 24.93/15.93  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 24.93/15.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.93/15.93  tff(f_212, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 24.93/15.93  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 24.93/15.93  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 24.93/15.93  tff(f_187, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 24.93/15.93  tff(f_254, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 24.93/15.93  tff(c_62, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_94, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_80, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_142, plain, (![B_291, A_292]: (l1_pre_topc(B_291) | ~m1_pre_topc(B_291, A_292) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.93/15.93  tff(c_151, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_142])).
% 24.93/15.93  tff(c_158, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_151])).
% 24.93/15.93  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 24.93/15.93  tff(c_124, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_48])).
% 24.93/15.93  tff(c_128, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_124])).
% 24.93/15.93  tff(c_166, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_158, c_128])).
% 24.93/15.93  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_180, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_70])).
% 24.93/15.93  tff(c_98, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_96, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_84, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_148, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_142])).
% 24.93/15.93  tff(c_155, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_148])).
% 24.93/15.93  tff(c_162, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_155, c_128])).
% 24.93/15.93  tff(c_215, plain, (![B_298, A_299]: (m1_subset_1(u1_struct_0(B_298), k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_194])).
% 24.93/15.93  tff(c_221, plain, (![B_298]: (m1_subset_1(u1_struct_0(B_298), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_298, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_215])).
% 24.93/15.93  tff(c_248, plain, (![B_300]: (m1_subset_1(u1_struct_0(B_300), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_300, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_221])).
% 24.93/15.93  tff(c_254, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_248])).
% 24.93/15.93  tff(c_377, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_254])).
% 24.93/15.93  tff(c_50, plain, (![A_86]: (m1_pre_topc(A_86, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_198])).
% 24.93/15.93  tff(c_72, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_173, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_72])).
% 24.93/15.93  tff(c_516, plain, (![A_316, B_317]: (m1_pre_topc(A_316, g1_pre_topc(u1_struct_0(B_317), u1_pre_topc(B_317))) | ~m1_pre_topc(A_316, B_317) | ~l1_pre_topc(B_317) | ~l1_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.93/15.93  tff(c_537, plain, (![A_316]: (m1_pre_topc(A_316, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_316, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_316))), inference(superposition, [status(thm), theory('equality')], [c_162, c_516])).
% 24.93/15.93  tff(c_565, plain, (![A_318]: (m1_pre_topc(A_318, '#skF_4') | ~m1_pre_topc(A_318, '#skF_3') | ~l1_pre_topc(A_318))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_173, c_537])).
% 24.93/15.93  tff(c_579, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_565])).
% 24.93/15.93  tff(c_590, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_579])).
% 24.93/15.93  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_590])).
% 24.93/15.93  tff(c_594, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_254])).
% 24.93/15.93  tff(c_262, plain, (![B_301, A_302]: (m1_pre_topc(B_301, A_302) | ~m1_pre_topc(B_301, g1_pre_topc(u1_struct_0(A_302), u1_pre_topc(A_302))) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_82])).
% 24.93/15.93  tff(c_268, plain, (![B_301]: (m1_pre_topc(B_301, '#skF_3') | ~m1_pre_topc(B_301, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_262])).
% 24.93/15.93  tff(c_282, plain, (![B_301]: (m1_pre_topc(B_301, '#skF_3') | ~m1_pre_topc(B_301, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_173, c_268])).
% 24.93/15.93  tff(c_227, plain, (![B_298]: (m1_subset_1(u1_struct_0(B_298), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_298, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_215])).
% 24.93/15.93  tff(c_363, plain, (![B_311]: (m1_subset_1(u1_struct_0(B_311), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_311, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_227])).
% 24.93/15.93  tff(c_366, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_166, c_363])).
% 24.93/15.93  tff(c_695, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_366])).
% 24.93/15.93  tff(c_699, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_282, c_695])).
% 24.93/15.93  tff(c_742, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_699])).
% 24.93/15.93  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_742])).
% 24.93/15.93  tff(c_748, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_366])).
% 24.93/15.93  tff(c_640, plain, (![A_320, B_321]: (m1_pre_topc(A_320, g1_pre_topc(u1_struct_0(B_321), u1_pre_topc(B_321))) | ~m1_pre_topc(A_320, B_321) | ~l1_pre_topc(B_321) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.93/15.93  tff(c_661, plain, (![A_320]: (m1_pre_topc(A_320, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_320, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_320))), inference(superposition, [status(thm), theory('equality')], [c_162, c_640])).
% 24.93/15.93  tff(c_678, plain, (![A_320]: (m1_pre_topc(A_320, '#skF_4') | ~m1_pre_topc(A_320, '#skF_3') | ~l1_pre_topc(A_320))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_173, c_661])).
% 24.93/15.93  tff(c_751, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_748, c_678])).
% 24.93/15.93  tff(c_762, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_751])).
% 24.93/15.93  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_88, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_129, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(resolution, [status(thm)], [c_16, c_124])).
% 24.93/15.93  tff(c_137, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_129])).
% 24.93/15.93  tff(c_76, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_167, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_76])).
% 24.93/15.93  tff(c_185, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_167])).
% 24.93/15.93  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_172, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_74])).
% 24.93/15.93  tff(c_179, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_172])).
% 24.93/15.93  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_198, plain, (![B_296, A_297]: (v2_pre_topc(B_296) | ~m1_pre_topc(B_296, A_297) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_44])).
% 24.93/15.93  tff(c_207, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_198])).
% 24.93/15.93  tff(c_214, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_207])).
% 24.93/15.93  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_90, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_2355, plain, (![A_395, B_396, C_397, D_398]: (k2_partfun1(u1_struct_0(A_395), u1_struct_0(B_396), C_397, u1_struct_0(D_398))=k2_tmap_1(A_395, B_396, C_397, D_398) | ~m1_pre_topc(D_398, A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0(B_396)))) | ~v1_funct_2(C_397, u1_struct_0(A_395), u1_struct_0(B_396)) | ~v1_funct_1(C_397) | ~l1_pre_topc(B_396) | ~v2_pre_topc(B_396) | v2_struct_0(B_396) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_137])).
% 24.93/15.93  tff(c_2367, plain, (![A_395, C_397, D_398]: (k2_partfun1(u1_struct_0(A_395), u1_struct_0('#skF_2'), C_397, u1_struct_0(D_398))=k2_tmap_1(A_395, '#skF_2', C_397, D_398) | ~m1_pre_topc(D_398, A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_397, u1_struct_0(A_395), u1_struct_0('#skF_2')) | ~v1_funct_1(C_397) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(superposition, [status(thm), theory('equality')], [c_137, c_2355])).
% 24.93/15.93  tff(c_2391, plain, (![A_395, C_397, D_398]: (k2_partfun1(u1_struct_0(A_395), k2_struct_0('#skF_2'), C_397, u1_struct_0(D_398))=k2_tmap_1(A_395, '#skF_2', C_397, D_398) | ~m1_pre_topc(D_398, A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_397, u1_struct_0(A_395), k2_struct_0('#skF_2')) | ~v1_funct_1(C_397) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_137, c_137, c_2367])).
% 24.93/15.93  tff(c_5390, plain, (![A_560, C_561, D_562]: (k2_partfun1(u1_struct_0(A_560), k2_struct_0('#skF_2'), C_561, u1_struct_0(D_562))=k2_tmap_1(A_560, '#skF_2', C_561, D_562) | ~m1_pre_topc(D_562, A_560) | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_560), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_561, u1_struct_0(A_560), k2_struct_0('#skF_2')) | ~v1_funct_1(C_561) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(negUnitSimplification, [status(thm)], [c_92, c_2391])).
% 24.93/15.93  tff(c_5394, plain, (![C_561, D_562]: (k2_partfun1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_561, u1_struct_0(D_562))=k2_tmap_1('#skF_4', '#skF_2', C_561, D_562) | ~m1_pre_topc(D_562, '#skF_4') | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_561, u1_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_561) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_5390])).
% 24.93/15.93  tff(c_5406, plain, (![C_561, D_562]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_561, u1_struct_0(D_562))=k2_tmap_1('#skF_4', '#skF_2', C_561, D_562) | ~m1_pre_topc(D_562, '#skF_4') | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_561, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_561) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_158, c_166, c_166, c_5394])).
% 24.93/15.93  tff(c_5855, plain, (![C_574, D_575]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_574, u1_struct_0(D_575))=k2_tmap_1('#skF_4', '#skF_2', C_574, D_575) | ~m1_pre_topc(D_575, '#skF_4') | ~m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_574, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_574))), inference(negUnitSimplification, [status(thm)], [c_82, c_5406])).
% 24.93/15.93  tff(c_5857, plain, (![D_575]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_575))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_575) | ~m1_pre_topc(D_575, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_179, c_5855])).
% 24.93/15.93  tff(c_5865, plain, (![D_576]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_576))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_576) | ~m1_pre_topc(D_576, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_185, c_5857])).
% 24.93/15.93  tff(c_5877, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_166, c_5865])).
% 24.93/15.93  tff(c_5889, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_5877])).
% 24.93/15.93  tff(c_204, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_198])).
% 24.93/15.93  tff(c_211, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_204])).
% 24.93/15.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.93/15.93  tff(c_862, plain, (![B_328, C_329, A_330]: (m1_pre_topc(B_328, C_329) | ~r1_tarski(u1_struct_0(B_328), u1_struct_0(C_329)) | ~m1_pre_topc(C_329, A_330) | ~m1_pre_topc(B_328, A_330) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_212])).
% 24.93/15.93  tff(c_884, plain, (![B_331, A_332]: (m1_pre_topc(B_331, B_331) | ~m1_pre_topc(B_331, A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332))), inference(resolution, [status(thm)], [c_6, c_862])).
% 24.93/15.93  tff(c_900, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_884])).
% 24.93/15.93  tff(c_920, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_900])).
% 24.93/15.93  tff(c_1011, plain, (![B_338, C_339, A_340]: (r1_tarski(u1_struct_0(B_338), u1_struct_0(C_339)) | ~m1_pre_topc(B_338, C_339) | ~m1_pre_topc(C_339, A_340) | ~m1_pre_topc(B_338, A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_212])).
% 24.93/15.93  tff(c_1013, plain, (![B_338]: (r1_tarski(u1_struct_0(B_338), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_338, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_920, c_1011])).
% 24.93/15.93  tff(c_1057, plain, (![B_341]: (r1_tarski(u1_struct_0(B_341), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_341, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_155, c_162, c_1013])).
% 24.93/15.93  tff(c_1062, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_166, c_1057])).
% 24.93/15.93  tff(c_1074, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_748, c_1062])).
% 24.93/15.93  tff(c_1017, plain, (![B_338]: (r1_tarski(u1_struct_0(B_338), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_338, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_762, c_1011])).
% 24.93/15.93  tff(c_1108, plain, (![B_344]: (r1_tarski(u1_struct_0(B_344), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_344, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_158, c_166, c_1017])).
% 24.93/15.93  tff(c_1116, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_1108])).
% 24.93/15.93  tff(c_1127, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_1116])).
% 24.93/15.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.93/15.93  tff(c_1129, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1127, c_2])).
% 24.93/15.93  tff(c_1132, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_1129])).
% 24.93/15.93  tff(c_1145, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_162])).
% 24.93/15.93  tff(c_2611, plain, (![B_413, D_410, C_414, E_411, A_412]: (k3_tmap_1(A_412, B_413, C_414, D_410, E_411)=k2_partfun1(u1_struct_0(C_414), u1_struct_0(B_413), E_411, u1_struct_0(D_410)) | ~m1_pre_topc(D_410, C_414) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_414), u1_struct_0(B_413)))) | ~v1_funct_2(E_411, u1_struct_0(C_414), u1_struct_0(B_413)) | ~v1_funct_1(E_411) | ~m1_pre_topc(D_410, A_412) | ~m1_pre_topc(C_414, A_412) | ~l1_pre_topc(B_413) | ~v2_pre_topc(B_413) | v2_struct_0(B_413) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_169])).
% 24.93/15.93  tff(c_2617, plain, (![A_412, B_413, D_410, E_411]: (k3_tmap_1(A_412, B_413, '#skF_4', D_410, E_411)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_413), E_411, u1_struct_0(D_410)) | ~m1_pre_topc(D_410, '#skF_4') | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_413)))) | ~v1_funct_2(E_411, u1_struct_0('#skF_4'), u1_struct_0(B_413)) | ~v1_funct_1(E_411) | ~m1_pre_topc(D_410, A_412) | ~m1_pre_topc('#skF_4', A_412) | ~l1_pre_topc(B_413) | ~v2_pre_topc(B_413) | v2_struct_0(B_413) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2611])).
% 24.93/15.93  tff(c_38559, plain, (![A_1202, B_1203, D_1204, E_1205]: (k3_tmap_1(A_1202, B_1203, '#skF_4', D_1204, E_1205)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_1203), E_1205, u1_struct_0(D_1204)) | ~m1_pre_topc(D_1204, '#skF_4') | ~m1_subset_1(E_1205, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_1203)))) | ~v1_funct_2(E_1205, k2_struct_0('#skF_4'), u1_struct_0(B_1203)) | ~v1_funct_1(E_1205) | ~m1_pre_topc(D_1204, A_1202) | ~m1_pre_topc('#skF_4', A_1202) | ~l1_pre_topc(B_1203) | ~v2_pre_topc(B_1203) | v2_struct_0(B_1203) | ~l1_pre_topc(A_1202) | ~v2_pre_topc(A_1202) | v2_struct_0(A_1202))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_2617])).
% 24.93/15.93  tff(c_38565, plain, (![A_1202, D_1204, E_1205]: (k3_tmap_1(A_1202, '#skF_2', '#skF_4', D_1204, E_1205)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_1205, u1_struct_0(D_1204)) | ~m1_pre_topc(D_1204, '#skF_4') | ~m1_subset_1(E_1205, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1205, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_1205) | ~m1_pre_topc(D_1204, A_1202) | ~m1_pre_topc('#skF_4', A_1202) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1202) | ~v2_pre_topc(A_1202) | v2_struct_0(A_1202))), inference(superposition, [status(thm), theory('equality')], [c_137, c_38559])).
% 24.93/15.93  tff(c_38578, plain, (![A_1202, D_1204, E_1205]: (k3_tmap_1(A_1202, '#skF_2', '#skF_4', D_1204, E_1205)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1205, u1_struct_0(D_1204)) | ~m1_pre_topc(D_1204, '#skF_4') | ~m1_subset_1(E_1205, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1205, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1205) | ~m1_pre_topc(D_1204, A_1202) | ~m1_pre_topc('#skF_4', A_1202) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1202) | ~v2_pre_topc(A_1202) | v2_struct_0(A_1202))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_137, c_137, c_38565])).
% 24.93/15.93  tff(c_58752, plain, (![A_1613, D_1614, E_1615]: (k3_tmap_1(A_1613, '#skF_2', '#skF_4', D_1614, E_1615)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1615, u1_struct_0(D_1614)) | ~m1_pre_topc(D_1614, '#skF_4') | ~m1_subset_1(E_1615, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1615, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1615) | ~m1_pre_topc(D_1614, A_1613) | ~m1_pre_topc('#skF_4', A_1613) | ~l1_pre_topc(A_1613) | ~v2_pre_topc(A_1613) | v2_struct_0(A_1613))), inference(negUnitSimplification, [status(thm)], [c_92, c_38578])).
% 24.93/15.93  tff(c_58754, plain, (![A_1613, D_1614]: (k3_tmap_1(A_1613, '#skF_2', '#skF_4', D_1614, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1614)) | ~m1_pre_topc(D_1614, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_1614, A_1613) | ~m1_pre_topc('#skF_4', A_1613) | ~l1_pre_topc(A_1613) | ~v2_pre_topc(A_1613) | v2_struct_0(A_1613))), inference(resolution, [status(thm)], [c_179, c_58752])).
% 24.93/15.93  tff(c_58762, plain, (![A_1616, D_1617]: (k3_tmap_1(A_1616, '#skF_2', '#skF_4', D_1617, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1617)) | ~m1_pre_topc(D_1617, '#skF_4') | ~m1_pre_topc(D_1617, A_1616) | ~m1_pre_topc('#skF_4', A_1616) | ~l1_pre_topc(A_1616) | ~v2_pre_topc(A_1616) | v2_struct_0(A_1616))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_185, c_58754])).
% 24.93/15.93  tff(c_58868, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_58762])).
% 24.93/15.93  tff(c_58997, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_594, c_5889, c_1145, c_58868])).
% 24.93/15.93  tff(c_58998, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_58997])).
% 24.93/15.93  tff(c_66, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_64, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_100, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64])).
% 24.93/15.93  tff(c_59064, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58998, c_100])).
% 24.93/15.93  tff(c_86, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.93/15.93  tff(c_36, plain, (![A_29]: (v3_pre_topc(k2_struct_0(A_29), A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 24.93/15.93  tff(c_48, plain, (![B_85, A_83]: (m1_subset_1(u1_struct_0(B_85), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_pre_topc(B_85, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_194])).
% 24.93/15.93  tff(c_1320, plain, (![B_353, A_354]: (v1_tsep_1(B_353, A_354) | ~v3_pre_topc(u1_struct_0(B_353), A_354) | ~m1_subset_1(u1_struct_0(B_353), k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_pre_topc(B_353, A_354) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_187])).
% 24.93/15.93  tff(c_2564, plain, (![B_407, A_408]: (v1_tsep_1(B_407, A_408) | ~v3_pre_topc(u1_struct_0(B_407), A_408) | ~v2_pre_topc(A_408) | ~m1_pre_topc(B_407, A_408) | ~l1_pre_topc(A_408))), inference(resolution, [status(thm)], [c_48, c_1320])).
% 24.93/15.93  tff(c_3872, plain, (![A_492]: (v1_tsep_1('#skF_3', A_492) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_492) | ~v2_pre_topc(A_492) | ~m1_pre_topc('#skF_3', A_492) | ~l1_pre_topc(A_492))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_2564])).
% 24.93/15.93  tff(c_3889, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3872])).
% 24.93/15.93  tff(c_3900, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_158, c_594, c_3889])).
% 24.93/15.93  tff(c_5874, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1145, c_5865])).
% 24.93/15.93  tff(c_5887, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_5874])).
% 24.93/15.93  tff(c_5894, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5889, c_5887])).
% 24.93/15.93  tff(c_56, plain, (![B_126, D_150, F_156, C_142, A_94]: (r1_tmap_1(B_126, A_94, C_142, F_156) | ~r1_tmap_1(D_150, A_94, k2_tmap_1(B_126, A_94, C_142, D_150), F_156) | ~m1_subset_1(F_156, u1_struct_0(D_150)) | ~m1_subset_1(F_156, u1_struct_0(B_126)) | ~m1_pre_topc(D_150, B_126) | ~v1_tsep_1(D_150, B_126) | v2_struct_0(D_150) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_126), u1_struct_0(A_94)))) | ~v1_funct_2(C_142, u1_struct_0(B_126), u1_struct_0(A_94)) | ~v1_funct_1(C_142) | ~l1_pre_topc(B_126) | ~v2_pre_topc(B_126) | v2_struct_0(B_126) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_254])).
% 24.93/15.93  tff(c_5897, plain, (![F_156]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_156) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_156) | ~m1_subset_1(F_156, u1_struct_0('#skF_3')) | ~m1_subset_1(F_156, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5894, c_56])).
% 24.93/15.93  tff(c_5901, plain, (![F_156]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_156) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_156) | ~m1_subset_1(F_156, k2_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_214, c_158, c_78, c_185, c_137, c_166, c_179, c_137, c_166, c_3900, c_594, c_166, c_1145, c_5897])).
% 24.93/15.93  tff(c_5902, plain, (![F_156]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_156) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_156) | ~m1_subset_1(F_156, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_92, c_82, c_86, c_5901])).
% 24.93/15.93  tff(c_59074, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_59064, c_5902])).
% 24.93/15.93  tff(c_59080, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_59074])).
% 24.93/15.93  tff(c_59082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_59080])).
% 24.93/15.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.93/15.93  
% 24.93/15.93  Inference rules
% 24.93/15.93  ----------------------
% 24.93/15.93  #Ref     : 0
% 24.93/15.93  #Sup     : 12693
% 24.93/15.93  #Fact    : 0
% 24.93/15.93  #Define  : 0
% 24.93/15.93  #Split   : 67
% 24.93/15.93  #Chain   : 0
% 24.93/15.93  #Close   : 0
% 24.93/15.93  
% 24.93/15.93  Ordering : KBO
% 24.93/15.93  
% 24.93/15.93  Simplification rules
% 24.93/15.93  ----------------------
% 24.93/15.93  #Subsume      : 8083
% 24.93/15.93  #Demod        : 28866
% 24.93/15.93  #Tautology    : 1714
% 24.93/15.93  #SimpNegUnit  : 948
% 24.93/15.93  #BackRed      : 18
% 24.93/15.93  
% 24.93/15.93  #Partial instantiations: 0
% 24.93/15.93  #Strategies tried      : 1
% 24.93/15.93  
% 24.93/15.93  Timing (in seconds)
% 24.93/15.94  ----------------------
% 24.93/15.94  Preprocessing        : 0.43
% 24.93/15.94  Parsing              : 0.21
% 24.93/15.94  CNF conversion       : 0.05
% 24.93/15.94  Main loop            : 14.69
% 24.93/15.94  Inferencing          : 2.17
% 24.93/15.94  Reduction            : 5.02
% 24.93/15.94  Demodulation         : 3.88
% 24.93/15.94  BG Simplification    : 0.15
% 24.93/15.94  Subsumption          : 6.84
% 24.93/15.94  Abstraction          : 0.45
% 24.93/15.94  MUC search           : 0.00
% 24.93/15.94  Cooper               : 0.00
% 24.93/15.94  Total                : 15.18
% 24.93/15.94  Index Insertion      : 0.00
% 24.93/15.94  Index Deletion       : 0.00
% 24.93/15.94  Index Matching       : 0.00
% 24.93/15.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
