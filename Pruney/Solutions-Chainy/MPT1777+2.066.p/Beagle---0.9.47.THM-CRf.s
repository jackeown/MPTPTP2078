%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 12.31s
% Output     : CNFRefutation 12.59s
% Verified   : 
% Statistics : Number of formulae       :  153 (1249 expanded)
%              Number of leaves         :   45 ( 455 expanded)
%              Depth                    :   26
%              Number of atoms          :  511 (6009 expanded)
%              Number of equality atoms :   39 ( 707 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_310,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_159,axiom,(
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

tff(f_155,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_148,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_98,axiom,(
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

tff(f_130,axiom,(
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

tff(f_261,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( ( F = G
                                    & r1_tmap_1(D,B,k2_tmap_1(A,B,E,D),F) )
                                 => r1_tmap_1(C,B,k2_tmap_1(A,B,E,C),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

tff(f_201,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_112,plain,(
    ! [B_394,A_395] :
      ( l1_pre_topc(B_394)
      | ~ m1_pre_topc(B_394,A_395)
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_128,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_121])).

tff(c_30,plain,(
    ! [A_72] :
      ( m1_pre_topc(A_72,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_392] :
      ( u1_struct_0(A_392) = k2_struct_0(A_392)
      | ~ l1_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_93])).

tff(c_173,plain,(
    ! [B_399,A_400] :
      ( m1_subset_1(u1_struct_0(B_399),k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ m1_pre_topc(B_399,A_400)
      | ~ l1_pre_topc(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_179,plain,(
    ! [B_399] :
      ( m1_subset_1(u1_struct_0(B_399),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_399,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_173])).

tff(c_206,plain,(
    ! [B_401] :
      ( m1_subset_1(u1_struct_0(B_401),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_401,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_179])).

tff(c_209,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_206])).

tff(c_318,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_321,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_318])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_321])).

tff(c_327,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_112])).

tff(c_125,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_118])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_93])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_138,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_249,plain,(
    ! [B_404,A_405] :
      ( m1_pre_topc(B_404,A_405)
      | ~ m1_pre_topc(B_404,g1_pre_topc(u1_struct_0(A_405),u1_pre_topc(A_405)))
      | ~ l1_pre_topc(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_255,plain,(
    ! [B_404] :
      ( m1_pre_topc(B_404,'#skF_3')
      | ~ m1_pre_topc(B_404,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_249])).

tff(c_269,plain,(
    ! [B_404] :
      ( m1_pre_topc(B_404,'#skF_3')
      | ~ m1_pre_topc(B_404,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_138,c_255])).

tff(c_185,plain,(
    ! [B_399] :
      ( m1_subset_1(u1_struct_0(B_399),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_399,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_173])).

tff(c_305,plain,(
    ! [B_409] :
      ( m1_subset_1(u1_struct_0(B_409),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_409,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_185])).

tff(c_308,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_305])).

tff(c_658,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_661,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_269,c_658])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_661])).

tff(c_667,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_147,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_156,plain,(
    ! [B_397,A_398] :
      ( v2_pre_topc(B_397)
      | ~ m1_pre_topc(B_397,A_398)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_165,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_156])).

tff(c_172,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_165])).

tff(c_16,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [B_71,A_69] :
      ( m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_pre_topc(B_71,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_611,plain,(
    ! [B_420,A_421] :
      ( v1_tsep_1(B_420,A_421)
      | ~ v3_pre_topc(u1_struct_0(B_420),A_421)
      | ~ m1_subset_1(u1_struct_0(B_420),k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1323,plain,(
    ! [B_465,A_466] :
      ( v1_tsep_1(B_465,A_466)
      | ~ v3_pre_topc(u1_struct_0(B_465),A_466)
      | ~ v2_pre_topc(A_466)
      | ~ m1_pre_topc(B_465,A_466)
      | ~ l1_pre_topc(A_466) ) ),
    inference(resolution,[status(thm)],[c_28,c_611])).

tff(c_1353,plain,(
    ! [A_469] :
      ( v1_tsep_1('#skF_4',A_469)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_469)
      | ~ v2_pre_topc(A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc(A_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1323])).

tff(c_1357,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1353])).

tff(c_1360,plain,(
    v1_tsep_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_128,c_327,c_1357])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_94,plain,(
    ! [A_393] :
      ( u1_struct_0(A_393) = k2_struct_0(A_393)
      | ~ l1_pre_topc(A_393) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_107,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_146,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_144,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_52])).

tff(c_145,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_144])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_411,plain,(
    ! [A_414,B_415] :
      ( m1_pre_topc(A_414,g1_pre_topc(u1_struct_0(B_415),u1_pre_topc(B_415)))
      | ~ m1_pre_topc(A_414,B_415)
      | ~ l1_pre_topc(B_415)
      | ~ l1_pre_topc(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_428,plain,(
    ! [A_414] :
      ( m1_pre_topc(A_414,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_414,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_411])).

tff(c_462,plain,(
    ! [A_416] :
      ( m1_pre_topc(A_416,'#skF_4')
      | ~ m1_pre_topc(A_416,'#skF_3')
      | ~ l1_pre_topc(A_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_138,c_428])).

tff(c_473,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_462])).

tff(c_480,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_473])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_139,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_77])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_713,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( k2_partfun1(u1_struct_0(A_422),u1_struct_0(B_423),C_424,u1_struct_0(D_425)) = k2_tmap_1(A_422,B_423,C_424,D_425)
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422),u1_struct_0(B_423))))
      | ~ v1_funct_2(C_424,u1_struct_0(A_422),u1_struct_0(B_423))
      | ~ v1_funct_1(C_424)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_715,plain,(
    ! [B_423,C_424,D_425] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_423),C_424,u1_struct_0(D_425)) = k2_tmap_1('#skF_4',B_423,C_424,D_425)
      | ~ m1_pre_topc(D_425,'#skF_4')
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_423))))
      | ~ v1_funct_2(C_424,u1_struct_0('#skF_4'),u1_struct_0(B_423))
      | ~ v1_funct_1(C_424)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_713])).

tff(c_731,plain,(
    ! [B_423,C_424,D_425] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_423),C_424,u1_struct_0(D_425)) = k2_tmap_1('#skF_4',B_423,C_424,D_425)
      | ~ m1_pre_topc(D_425,'#skF_4')
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_423))))
      | ~ v1_funct_2(C_424,k2_struct_0('#skF_4'),u1_struct_0(B_423))
      | ~ v1_funct_1(C_424)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_128,c_137,c_137,c_715])).

tff(c_5326,plain,(
    ! [B_610,C_611,D_612] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_610),C_611,u1_struct_0(D_612)) = k2_tmap_1('#skF_4',B_610,C_611,D_612)
      | ~ m1_pre_topc(D_612,'#skF_4')
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_610))))
      | ~ v1_funct_2(C_611,k2_struct_0('#skF_4'),u1_struct_0(B_610))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_610)
      | ~ v2_pre_topc(B_610)
      | v2_struct_0(B_610) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_731])).

tff(c_5332,plain,(
    ! [C_611,D_612] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_611,u1_struct_0(D_612)) = k2_tmap_1('#skF_4','#skF_2',C_611,D_612)
      | ~ m1_pre_topc(D_612,'#skF_4')
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_611,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_5326])).

tff(c_5342,plain,(
    ! [C_611,D_612] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_611,u1_struct_0(D_612)) = k2_tmap_1('#skF_4','#skF_2',C_611,D_612)
      | ~ m1_pre_topc(D_612,'#skF_4')
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_611,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_611)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_102,c_102,c_5332])).

tff(c_5858,plain,(
    ! [C_624,D_625] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_624,u1_struct_0(D_625)) = k2_tmap_1('#skF_4','#skF_2',C_624,D_625)
      | ~ m1_pre_topc(D_625,'#skF_4')
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_624,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_624) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5342])).

tff(c_5860,plain,(
    ! [D_625] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_625)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_625)
      | ~ m1_pre_topc(D_625,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_5858])).

tff(c_5864,plain,(
    ! [D_626] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_626)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_626)
      | ~ m1_pre_topc(D_626,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_146,c_5860])).

tff(c_5876,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_5864])).

tff(c_5888,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_5876])).

tff(c_967,plain,(
    ! [C_435,A_438,D_439,E_436,B_437] :
      ( k3_tmap_1(A_438,B_437,C_435,D_439,E_436) = k2_partfun1(u1_struct_0(C_435),u1_struct_0(B_437),E_436,u1_struct_0(D_439))
      | ~ m1_pre_topc(D_439,C_435)
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_435),u1_struct_0(B_437))))
      | ~ v1_funct_2(E_436,u1_struct_0(C_435),u1_struct_0(B_437))
      | ~ v1_funct_1(E_436)
      | ~ m1_pre_topc(D_439,A_438)
      | ~ m1_pre_topc(C_435,A_438)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_969,plain,(
    ! [A_438,B_437,D_439,E_436] :
      ( k3_tmap_1(A_438,B_437,'#skF_4',D_439,E_436) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_437),E_436,u1_struct_0(D_439))
      | ~ m1_pre_topc(D_439,'#skF_4')
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_437))))
      | ~ v1_funct_2(E_436,u1_struct_0('#skF_4'),u1_struct_0(B_437))
      | ~ v1_funct_1(E_436)
      | ~ m1_pre_topc(D_439,A_438)
      | ~ m1_pre_topc('#skF_4',A_438)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_967])).

tff(c_11930,plain,(
    ! [A_748,B_749,D_750,E_751] :
      ( k3_tmap_1(A_748,B_749,'#skF_4',D_750,E_751) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_749),E_751,u1_struct_0(D_750))
      | ~ m1_pre_topc(D_750,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_749))))
      | ~ v1_funct_2(E_751,k2_struct_0('#skF_4'),u1_struct_0(B_749))
      | ~ v1_funct_1(E_751)
      | ~ m1_pre_topc(D_750,A_748)
      | ~ m1_pre_topc('#skF_4',A_748)
      | ~ l1_pre_topc(B_749)
      | ~ v2_pre_topc(B_749)
      | v2_struct_0(B_749)
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_137,c_969])).

tff(c_11936,plain,(
    ! [A_748,D_750,E_751] :
      ( k3_tmap_1(A_748,'#skF_2','#skF_4',D_750,E_751) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_751,u1_struct_0(D_750))
      | ~ m1_pre_topc(D_750,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_751,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_751)
      | ~ m1_pre_topc(D_750,A_748)
      | ~ m1_pre_topc('#skF_4',A_748)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_11930])).

tff(c_11946,plain,(
    ! [A_748,D_750,E_751] :
      ( k3_tmap_1(A_748,'#skF_2','#skF_4',D_750,E_751) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_751,u1_struct_0(D_750))
      | ~ m1_pre_topc(D_750,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_751,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_751)
      | ~ m1_pre_topc(D_750,A_748)
      | ~ m1_pre_topc('#skF_4',A_748)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_102,c_102,c_11936])).

tff(c_19578,plain,(
    ! [A_918,D_919,E_920] :
      ( k3_tmap_1(A_918,'#skF_2','#skF_4',D_919,E_920) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_920,u1_struct_0(D_919))
      | ~ m1_pre_topc(D_919,'#skF_4')
      | ~ m1_subset_1(E_920,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_920,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_920)
      | ~ m1_pre_topc(D_919,A_918)
      | ~ m1_pre_topc('#skF_4',A_918)
      | ~ l1_pre_topc(A_918)
      | ~ v2_pre_topc(A_918)
      | v2_struct_0(A_918) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_11946])).

tff(c_19580,plain,(
    ! [A_918,D_919] :
      ( k3_tmap_1(A_918,'#skF_2','#skF_4',D_919,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_919))
      | ~ m1_pre_topc(D_919,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_919,A_918)
      | ~ m1_pre_topc('#skF_4',A_918)
      | ~ l1_pre_topc(A_918)
      | ~ v2_pre_topc(A_918)
      | v2_struct_0(A_918) ) ),
    inference(resolution,[status(thm)],[c_145,c_19578])).

tff(c_20199,plain,(
    ! [A_927,D_928] :
      ( k3_tmap_1(A_927,'#skF_2','#skF_4',D_928,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_928))
      | ~ m1_pre_topc(D_928,'#skF_4')
      | ~ m1_pre_topc(D_928,A_927)
      | ~ m1_pre_topc('#skF_4',A_927)
      | ~ l1_pre_topc(A_927)
      | ~ v2_pre_topc(A_927)
      | v2_struct_0(A_927) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_146,c_19580])).

tff(c_20297,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_20199])).

tff(c_20414,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_58,c_480,c_5888,c_133,c_20297])).

tff(c_20415,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20414])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_20453,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20415,c_78])).

tff(c_38,plain,(
    ! [E_263,A_143,D_255,G_269,C_239,B_207] :
      ( r1_tmap_1(C_239,B_207,k2_tmap_1(A_143,B_207,E_263,C_239),G_269)
      | ~ r1_tmap_1(D_255,B_207,k2_tmap_1(A_143,B_207,E_263,D_255),G_269)
      | ~ m1_subset_1(G_269,u1_struct_0(C_239))
      | ~ m1_subset_1(G_269,u1_struct_0(D_255))
      | ~ m1_pre_topc(C_239,D_255)
      | ~ m1_subset_1(E_263,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143),u1_struct_0(B_207))))
      | ~ v1_funct_2(E_263,u1_struct_0(A_143),u1_struct_0(B_207))
      | ~ v1_funct_1(E_263)
      | ~ m1_pre_topc(D_255,A_143)
      | v2_struct_0(D_255)
      | ~ m1_pre_topc(C_239,A_143)
      | v2_struct_0(C_239)
      | ~ l1_pre_topc(B_207)
      | ~ v2_pre_topc(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_20463,plain,(
    ! [C_239] :
      ( r1_tmap_1(C_239,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',C_239),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_239))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(C_239,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_239,'#skF_4')
      | v2_struct_0(C_239)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20453,c_38])).

tff(c_20468,plain,(
    ! [C_239] :
      ( r1_tmap_1(C_239,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',C_239),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_239))
      | ~ m1_pre_topc(C_239,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_239,'#skF_4')
      | v2_struct_0(C_239)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_128,c_68,c_66,c_480,c_56,c_146,c_102,c_137,c_145,c_102,c_137,c_139,c_133,c_20463])).

tff(c_20781,plain,(
    ! [C_941] :
      ( r1_tmap_1(C_941,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',C_941),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_941))
      | ~ m1_pre_topc(C_941,'#skF_3')
      | ~ m1_pre_topc(C_941,'#skF_4')
      | v2_struct_0(C_941) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_70,c_64,c_20468])).

tff(c_32,plain,(
    ! [C_121,F_135,B_105,D_129,A_73] :
      ( r1_tmap_1(B_105,A_73,C_121,F_135)
      | ~ r1_tmap_1(D_129,A_73,k2_tmap_1(B_105,A_73,C_121,D_129),F_135)
      | ~ m1_subset_1(F_135,u1_struct_0(D_129))
      | ~ m1_subset_1(F_135,u1_struct_0(B_105))
      | ~ m1_pre_topc(D_129,B_105)
      | ~ v1_tsep_1(D_129,B_105)
      | v2_struct_0(D_129)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_105),u1_struct_0(A_73))))
      | ~ v1_funct_2(C_121,u1_struct_0(B_105),u1_struct_0(A_73))
      | ~ v1_funct_1(C_121)
      | ~ l1_pre_topc(B_105)
      | ~ v2_pre_topc(B_105)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_20785,plain,(
    ! [C_941] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ v1_tsep_1(C_941,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_941))
      | ~ m1_pre_topc(C_941,'#skF_3')
      | ~ m1_pre_topc(C_941,'#skF_4')
      | v2_struct_0(C_941) ) ),
    inference(resolution,[status(thm)],[c_20781,c_32])).

tff(c_20792,plain,(
    ! [C_941] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ v1_tsep_1(C_941,'#skF_4')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_941))
      | ~ m1_pre_topc(C_941,'#skF_3')
      | ~ m1_pre_topc(C_941,'#skF_4')
      | v2_struct_0(C_941) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_172,c_128,c_56,c_146,c_102,c_137,c_145,c_102,c_137,c_147,c_137,c_20785])).

tff(c_20794,plain,(
    ! [C_942] :
      ( ~ v1_tsep_1(C_942,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0(C_942))
      | ~ m1_pre_topc(C_942,'#skF_3')
      | ~ m1_pre_topc(C_942,'#skF_4')
      | v2_struct_0(C_942) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_60,c_40,c_20792])).

tff(c_20797,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_20794])).

tff(c_20808,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_667,c_147,c_1360,c_20797])).

tff(c_20810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_20808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:26:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.31/5.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.31/5.67  
% 12.31/5.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.31/5.68  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.31/5.68  
% 12.31/5.68  %Foreground sorts:
% 12.31/5.68  
% 12.31/5.68  
% 12.31/5.68  %Background operators:
% 12.31/5.68  
% 12.31/5.68  
% 12.31/5.68  %Foreground operators:
% 12.31/5.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.31/5.68  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.31/5.68  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.31/5.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.31/5.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.31/5.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.31/5.68  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.31/5.68  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 12.31/5.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.31/5.68  tff('#skF_7', type, '#skF_7': $i).
% 12.31/5.68  tff('#skF_5', type, '#skF_5': $i).
% 12.31/5.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.31/5.68  tff('#skF_6', type, '#skF_6': $i).
% 12.31/5.68  tff('#skF_2', type, '#skF_2': $i).
% 12.31/5.68  tff('#skF_3', type, '#skF_3': $i).
% 12.31/5.68  tff('#skF_1', type, '#skF_1': $i).
% 12.31/5.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.31/5.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.31/5.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.31/5.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.31/5.68  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 12.31/5.68  tff('#skF_4', type, '#skF_4': $i).
% 12.31/5.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.31/5.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.31/5.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.31/5.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.31/5.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.31/5.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.31/5.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.31/5.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.31/5.68  
% 12.59/5.70  tff(f_310, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 12.59/5.70  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.59/5.70  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.59/5.70  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.59/5.70  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.59/5.70  tff(f_155, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.59/5.70  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 12.59/5.70  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 12.59/5.70  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 12.59/5.70  tff(f_148, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 12.59/5.70  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 12.59/5.70  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 12.59/5.70  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 12.59/5.70  tff(f_261, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 12.59/5.70  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 12.59/5.70  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_112, plain, (![B_394, A_395]: (l1_pre_topc(B_394) | ~m1_pre_topc(B_394, A_395) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.59/5.70  tff(c_121, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_112])).
% 12.59/5.70  tff(c_128, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_121])).
% 12.59/5.70  tff(c_30, plain, (![A_72]: (m1_pre_topc(A_72, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.59/5.70  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.59/5.70  tff(c_89, plain, (![A_392]: (u1_struct_0(A_392)=k2_struct_0(A_392) | ~l1_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.59/5.70  tff(c_93, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_89])).
% 12.59/5.70  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_128, c_93])).
% 12.59/5.70  tff(c_173, plain, (![B_399, A_400]: (m1_subset_1(u1_struct_0(B_399), k1_zfmisc_1(u1_struct_0(A_400))) | ~m1_pre_topc(B_399, A_400) | ~l1_pre_topc(A_400))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.59/5.70  tff(c_179, plain, (![B_399]: (m1_subset_1(u1_struct_0(B_399), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_399, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_173])).
% 12.59/5.70  tff(c_206, plain, (![B_401]: (m1_subset_1(u1_struct_0(B_401), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_401, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_179])).
% 12.59/5.70  tff(c_209, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_206])).
% 12.59/5.70  tff(c_318, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 12.59/5.70  tff(c_321, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_318])).
% 12.59/5.70  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_321])).
% 12.59/5.70  tff(c_327, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_209])).
% 12.59/5.70  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_118, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_112])).
% 12.59/5.70  tff(c_125, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_118])).
% 12.59/5.70  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_93])).
% 12.59/5.70  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_138, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 12.59/5.70  tff(c_249, plain, (![B_404, A_405]: (m1_pre_topc(B_404, A_405) | ~m1_pre_topc(B_404, g1_pre_topc(u1_struct_0(A_405), u1_pre_topc(A_405))) | ~l1_pre_topc(A_405))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.59/5.70  tff(c_255, plain, (![B_404]: (m1_pre_topc(B_404, '#skF_3') | ~m1_pre_topc(B_404, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_249])).
% 12.59/5.70  tff(c_269, plain, (![B_404]: (m1_pre_topc(B_404, '#skF_3') | ~m1_pre_topc(B_404, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_138, c_255])).
% 12.59/5.70  tff(c_185, plain, (![B_399]: (m1_subset_1(u1_struct_0(B_399), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_399, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_173])).
% 12.59/5.70  tff(c_305, plain, (![B_409]: (m1_subset_1(u1_struct_0(B_409), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_409, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_185])).
% 12.59/5.70  tff(c_308, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_305])).
% 12.59/5.70  tff(c_658, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_308])).
% 12.59/5.70  tff(c_661, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_269, c_658])).
% 12.59/5.70  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_661])).
% 12.59/5.70  tff(c_667, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_308])).
% 12.59/5.70  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_147, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48])).
% 12.59/5.70  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_156, plain, (![B_397, A_398]: (v2_pre_topc(B_397) | ~m1_pre_topc(B_397, A_398) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.59/5.70  tff(c_165, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_156])).
% 12.59/5.70  tff(c_172, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_165])).
% 12.59/5.70  tff(c_16, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.59/5.70  tff(c_28, plain, (![B_71, A_69]: (m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_pre_topc(B_71, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.59/5.70  tff(c_611, plain, (![B_420, A_421]: (v1_tsep_1(B_420, A_421) | ~v3_pre_topc(u1_struct_0(B_420), A_421) | ~m1_subset_1(u1_struct_0(B_420), k1_zfmisc_1(u1_struct_0(A_421))) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.59/5.70  tff(c_1323, plain, (![B_465, A_466]: (v1_tsep_1(B_465, A_466) | ~v3_pre_topc(u1_struct_0(B_465), A_466) | ~v2_pre_topc(A_466) | ~m1_pre_topc(B_465, A_466) | ~l1_pre_topc(A_466))), inference(resolution, [status(thm)], [c_28, c_611])).
% 12.59/5.70  tff(c_1353, plain, (![A_469]: (v1_tsep_1('#skF_4', A_469) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_469) | ~v2_pre_topc(A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc(A_469))), inference(superposition, [status(thm), theory('equality')], [c_137, c_1323])).
% 12.59/5.70  tff(c_1357, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1353])).
% 12.59/5.70  tff(c_1360, plain, (v1_tsep_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_128, c_327, c_1357])).
% 12.59/5.70  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_94, plain, (![A_393]: (u1_struct_0(A_393)=k2_struct_0(A_393) | ~l1_pre_topc(A_393))), inference(resolution, [status(thm)], [c_6, c_89])).
% 12.59/5.70  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_94])).
% 12.59/5.70  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_107, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54])).
% 12.59/5.70  tff(c_146, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 12.59/5.70  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_144, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_52])).
% 12.59/5.70  tff(c_145, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_144])).
% 12.59/5.70  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_411, plain, (![A_414, B_415]: (m1_pre_topc(A_414, g1_pre_topc(u1_struct_0(B_415), u1_pre_topc(B_415))) | ~m1_pre_topc(A_414, B_415) | ~l1_pre_topc(B_415) | ~l1_pre_topc(A_414))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.59/5.70  tff(c_428, plain, (![A_414]: (m1_pre_topc(A_414, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_414, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_414))), inference(superposition, [status(thm), theory('equality')], [c_133, c_411])).
% 12.59/5.70  tff(c_462, plain, (![A_416]: (m1_pre_topc(A_416, '#skF_4') | ~m1_pre_topc(A_416, '#skF_3') | ~l1_pre_topc(A_416))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_138, c_428])).
% 12.59/5.70  tff(c_473, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_462])).
% 12.59/5.70  tff(c_480, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_473])).
% 12.59/5.70  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 12.59/5.70  tff(c_139, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_77])).
% 12.59/5.70  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_713, plain, (![A_422, B_423, C_424, D_425]: (k2_partfun1(u1_struct_0(A_422), u1_struct_0(B_423), C_424, u1_struct_0(D_425))=k2_tmap_1(A_422, B_423, C_424, D_425) | ~m1_pre_topc(D_425, A_422) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422), u1_struct_0(B_423)))) | ~v1_funct_2(C_424, u1_struct_0(A_422), u1_struct_0(B_423)) | ~v1_funct_1(C_424) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.59/5.70  tff(c_715, plain, (![B_423, C_424, D_425]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_423), C_424, u1_struct_0(D_425))=k2_tmap_1('#skF_4', B_423, C_424, D_425) | ~m1_pre_topc(D_425, '#skF_4') | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_423)))) | ~v1_funct_2(C_424, u1_struct_0('#skF_4'), u1_struct_0(B_423)) | ~v1_funct_1(C_424) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_713])).
% 12.59/5.70  tff(c_731, plain, (![B_423, C_424, D_425]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_423), C_424, u1_struct_0(D_425))=k2_tmap_1('#skF_4', B_423, C_424, D_425) | ~m1_pre_topc(D_425, '#skF_4') | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_423)))) | ~v1_funct_2(C_424, k2_struct_0('#skF_4'), u1_struct_0(B_423)) | ~v1_funct_1(C_424) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_128, c_137, c_137, c_715])).
% 12.59/5.70  tff(c_5326, plain, (![B_610, C_611, D_612]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_610), C_611, u1_struct_0(D_612))=k2_tmap_1('#skF_4', B_610, C_611, D_612) | ~m1_pre_topc(D_612, '#skF_4') | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_610)))) | ~v1_funct_2(C_611, k2_struct_0('#skF_4'), u1_struct_0(B_610)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_610) | ~v2_pre_topc(B_610) | v2_struct_0(B_610))), inference(negUnitSimplification, [status(thm)], [c_60, c_731])).
% 12.59/5.70  tff(c_5332, plain, (![C_611, D_612]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_611, u1_struct_0(D_612))=k2_tmap_1('#skF_4', '#skF_2', C_611, D_612) | ~m1_pre_topc(D_612, '#skF_4') | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_611, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_611) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_5326])).
% 12.59/5.70  tff(c_5342, plain, (![C_611, D_612]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_611, u1_struct_0(D_612))=k2_tmap_1('#skF_4', '#skF_2', C_611, D_612) | ~m1_pre_topc(D_612, '#skF_4') | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_611, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_611) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_102, c_102, c_5332])).
% 12.59/5.70  tff(c_5858, plain, (![C_624, D_625]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_624, u1_struct_0(D_625))=k2_tmap_1('#skF_4', '#skF_2', C_624, D_625) | ~m1_pre_topc(D_625, '#skF_4') | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_624, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_624))), inference(negUnitSimplification, [status(thm)], [c_70, c_5342])).
% 12.59/5.70  tff(c_5860, plain, (![D_625]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_625))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_625) | ~m1_pre_topc(D_625, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_145, c_5858])).
% 12.59/5.70  tff(c_5864, plain, (![D_626]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_626))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_626) | ~m1_pre_topc(D_626, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_146, c_5860])).
% 12.59/5.70  tff(c_5876, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_5864])).
% 12.59/5.70  tff(c_5888, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_5876])).
% 12.59/5.70  tff(c_967, plain, (![C_435, A_438, D_439, E_436, B_437]: (k3_tmap_1(A_438, B_437, C_435, D_439, E_436)=k2_partfun1(u1_struct_0(C_435), u1_struct_0(B_437), E_436, u1_struct_0(D_439)) | ~m1_pre_topc(D_439, C_435) | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_435), u1_struct_0(B_437)))) | ~v1_funct_2(E_436, u1_struct_0(C_435), u1_struct_0(B_437)) | ~v1_funct_1(E_436) | ~m1_pre_topc(D_439, A_438) | ~m1_pre_topc(C_435, A_438) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.59/5.70  tff(c_969, plain, (![A_438, B_437, D_439, E_436]: (k3_tmap_1(A_438, B_437, '#skF_4', D_439, E_436)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_437), E_436, u1_struct_0(D_439)) | ~m1_pre_topc(D_439, '#skF_4') | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_437)))) | ~v1_funct_2(E_436, u1_struct_0('#skF_4'), u1_struct_0(B_437)) | ~v1_funct_1(E_436) | ~m1_pre_topc(D_439, A_438) | ~m1_pre_topc('#skF_4', A_438) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(superposition, [status(thm), theory('equality')], [c_137, c_967])).
% 12.59/5.70  tff(c_11930, plain, (![A_748, B_749, D_750, E_751]: (k3_tmap_1(A_748, B_749, '#skF_4', D_750, E_751)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_749), E_751, u1_struct_0(D_750)) | ~m1_pre_topc(D_750, '#skF_4') | ~m1_subset_1(E_751, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_749)))) | ~v1_funct_2(E_751, k2_struct_0('#skF_4'), u1_struct_0(B_749)) | ~v1_funct_1(E_751) | ~m1_pre_topc(D_750, A_748) | ~m1_pre_topc('#skF_4', A_748) | ~l1_pre_topc(B_749) | ~v2_pre_topc(B_749) | v2_struct_0(B_749) | ~l1_pre_topc(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_137, c_969])).
% 12.59/5.70  tff(c_11936, plain, (![A_748, D_750, E_751]: (k3_tmap_1(A_748, '#skF_2', '#skF_4', D_750, E_751)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_751, u1_struct_0(D_750)) | ~m1_pre_topc(D_750, '#skF_4') | ~m1_subset_1(E_751, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_751, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_751) | ~m1_pre_topc(D_750, A_748) | ~m1_pre_topc('#skF_4', A_748) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748))), inference(superposition, [status(thm), theory('equality')], [c_102, c_11930])).
% 12.59/5.70  tff(c_11946, plain, (![A_748, D_750, E_751]: (k3_tmap_1(A_748, '#skF_2', '#skF_4', D_750, E_751)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_751, u1_struct_0(D_750)) | ~m1_pre_topc(D_750, '#skF_4') | ~m1_subset_1(E_751, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_751, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_751) | ~m1_pre_topc(D_750, A_748) | ~m1_pre_topc('#skF_4', A_748) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_102, c_102, c_11936])).
% 12.59/5.70  tff(c_19578, plain, (![A_918, D_919, E_920]: (k3_tmap_1(A_918, '#skF_2', '#skF_4', D_919, E_920)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_920, u1_struct_0(D_919)) | ~m1_pre_topc(D_919, '#skF_4') | ~m1_subset_1(E_920, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_920, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_920) | ~m1_pre_topc(D_919, A_918) | ~m1_pre_topc('#skF_4', A_918) | ~l1_pre_topc(A_918) | ~v2_pre_topc(A_918) | v2_struct_0(A_918))), inference(negUnitSimplification, [status(thm)], [c_70, c_11946])).
% 12.59/5.70  tff(c_19580, plain, (![A_918, D_919]: (k3_tmap_1(A_918, '#skF_2', '#skF_4', D_919, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_919)) | ~m1_pre_topc(D_919, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_919, A_918) | ~m1_pre_topc('#skF_4', A_918) | ~l1_pre_topc(A_918) | ~v2_pre_topc(A_918) | v2_struct_0(A_918))), inference(resolution, [status(thm)], [c_145, c_19578])).
% 12.59/5.70  tff(c_20199, plain, (![A_927, D_928]: (k3_tmap_1(A_927, '#skF_2', '#skF_4', D_928, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_928)) | ~m1_pre_topc(D_928, '#skF_4') | ~m1_pre_topc(D_928, A_927) | ~m1_pre_topc('#skF_4', A_927) | ~l1_pre_topc(A_927) | ~v2_pre_topc(A_927) | v2_struct_0(A_927))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_146, c_19580])).
% 12.59/5.70  tff(c_20297, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_20199])).
% 12.59/5.70  tff(c_20414, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_58, c_480, c_5888, c_133, c_20297])).
% 12.59/5.70  tff(c_20415, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_20414])).
% 12.59/5.70  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_310])).
% 12.59/5.70  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 12.59/5.70  tff(c_20453, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20415, c_78])).
% 12.59/5.70  tff(c_38, plain, (![E_263, A_143, D_255, G_269, C_239, B_207]: (r1_tmap_1(C_239, B_207, k2_tmap_1(A_143, B_207, E_263, C_239), G_269) | ~r1_tmap_1(D_255, B_207, k2_tmap_1(A_143, B_207, E_263, D_255), G_269) | ~m1_subset_1(G_269, u1_struct_0(C_239)) | ~m1_subset_1(G_269, u1_struct_0(D_255)) | ~m1_pre_topc(C_239, D_255) | ~m1_subset_1(E_263, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143), u1_struct_0(B_207)))) | ~v1_funct_2(E_263, u1_struct_0(A_143), u1_struct_0(B_207)) | ~v1_funct_1(E_263) | ~m1_pre_topc(D_255, A_143) | v2_struct_0(D_255) | ~m1_pre_topc(C_239, A_143) | v2_struct_0(C_239) | ~l1_pre_topc(B_207) | ~v2_pre_topc(B_207) | v2_struct_0(B_207) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_261])).
% 12.59/5.70  tff(c_20463, plain, (![C_239]: (r1_tmap_1(C_239, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_239), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(C_239)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc(C_239, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc(C_239, '#skF_4') | v2_struct_0(C_239) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20453, c_38])).
% 12.59/5.70  tff(c_20468, plain, (![C_239]: (r1_tmap_1(C_239, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_239), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(C_239)) | ~m1_pre_topc(C_239, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(C_239, '#skF_4') | v2_struct_0(C_239) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_128, c_68, c_66, c_480, c_56, c_146, c_102, c_137, c_145, c_102, c_137, c_139, c_133, c_20463])).
% 12.59/5.70  tff(c_20781, plain, (![C_941]: (r1_tmap_1(C_941, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_941), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(C_941)) | ~m1_pre_topc(C_941, '#skF_3') | ~m1_pre_topc(C_941, '#skF_4') | v2_struct_0(C_941))), inference(negUnitSimplification, [status(thm)], [c_60, c_70, c_64, c_20468])).
% 12.59/5.70  tff(c_32, plain, (![C_121, F_135, B_105, D_129, A_73]: (r1_tmap_1(B_105, A_73, C_121, F_135) | ~r1_tmap_1(D_129, A_73, k2_tmap_1(B_105, A_73, C_121, D_129), F_135) | ~m1_subset_1(F_135, u1_struct_0(D_129)) | ~m1_subset_1(F_135, u1_struct_0(B_105)) | ~m1_pre_topc(D_129, B_105) | ~v1_tsep_1(D_129, B_105) | v2_struct_0(D_129) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_105), u1_struct_0(A_73)))) | ~v1_funct_2(C_121, u1_struct_0(B_105), u1_struct_0(A_73)) | ~v1_funct_1(C_121) | ~l1_pre_topc(B_105) | ~v2_pre_topc(B_105) | v2_struct_0(B_105) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_201])).
% 12.59/5.70  tff(c_20785, plain, (![C_941]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~v1_tsep_1(C_941, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0(C_941)) | ~m1_pre_topc(C_941, '#skF_3') | ~m1_pre_topc(C_941, '#skF_4') | v2_struct_0(C_941))), inference(resolution, [status(thm)], [c_20781, c_32])).
% 12.59/5.70  tff(c_20792, plain, (![C_941]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1(C_941, '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0(C_941)) | ~m1_pre_topc(C_941, '#skF_3') | ~m1_pre_topc(C_941, '#skF_4') | v2_struct_0(C_941))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_172, c_128, c_56, c_146, c_102, c_137, c_145, c_102, c_137, c_147, c_137, c_20785])).
% 12.59/5.70  tff(c_20794, plain, (![C_942]: (~v1_tsep_1(C_942, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0(C_942)) | ~m1_pre_topc(C_942, '#skF_3') | ~m1_pre_topc(C_942, '#skF_4') | v2_struct_0(C_942))), inference(negUnitSimplification, [status(thm)], [c_70, c_60, c_40, c_20792])).
% 12.59/5.70  tff(c_20797, plain, (~v1_tsep_1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_20794])).
% 12.59/5.70  tff(c_20808, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_667, c_147, c_1360, c_20797])).
% 12.59/5.70  tff(c_20810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_20808])).
% 12.59/5.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.59/5.70  
% 12.59/5.70  Inference rules
% 12.59/5.70  ----------------------
% 12.59/5.70  #Ref     : 0
% 12.59/5.70  #Sup     : 4584
% 12.59/5.70  #Fact    : 0
% 12.59/5.70  #Define  : 0
% 12.59/5.70  #Split   : 20
% 12.59/5.70  #Chain   : 0
% 12.59/5.70  #Close   : 0
% 12.59/5.70  
% 12.59/5.70  Ordering : KBO
% 12.59/5.70  
% 12.59/5.70  Simplification rules
% 12.59/5.70  ----------------------
% 12.59/5.70  #Subsume      : 2716
% 12.59/5.70  #Demod        : 8948
% 12.59/5.70  #Tautology    : 783
% 12.59/5.70  #SimpNegUnit  : 234
% 12.59/5.70  #BackRed      : 7
% 12.59/5.70  
% 12.59/5.70  #Partial instantiations: 0
% 12.59/5.70  #Strategies tried      : 1
% 12.59/5.70  
% 12.59/5.70  Timing (in seconds)
% 12.59/5.70  ----------------------
% 12.59/5.71  Preprocessing        : 0.41
% 12.59/5.71  Parsing              : 0.22
% 12.59/5.71  CNF conversion       : 0.05
% 12.59/5.71  Main loop            : 4.55
% 12.59/5.71  Inferencing          : 0.76
% 12.59/5.71  Reduction            : 1.60
% 12.59/5.71  Demodulation         : 1.22
% 12.59/5.71  BG Simplification    : 0.07
% 12.59/5.71  Subsumption          : 1.97
% 12.59/5.71  Abstraction          : 0.17
% 12.59/5.71  MUC search           : 0.00
% 12.59/5.71  Cooper               : 0.00
% 12.59/5.71  Total                : 5.01
% 12.59/5.71  Index Insertion      : 0.00
% 12.59/5.71  Index Deletion       : 0.00
% 12.59/5.71  Index Matching       : 0.00
% 12.59/5.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
