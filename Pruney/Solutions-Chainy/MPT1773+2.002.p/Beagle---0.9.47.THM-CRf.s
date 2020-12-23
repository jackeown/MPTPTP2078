%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 948 expanded)
%              Number of leaves         :   42 ( 381 expanded)
%              Depth                    :   17
%              Number of atoms          :  547 (8730 expanded)
%              Number of equality atoms :   45 ( 462 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_313,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,D)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_144,axiom,(
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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_195,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_255,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_34,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_36,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_38,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_86,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_128,plain,(
    ! [B_587,A_588] :
      ( v2_pre_topc(B_587)
      | ~ m1_pre_topc(B_587,A_588)
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_140,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_128])).

tff(c_150,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_140])).

tff(c_94,plain,(
    ! [B_583,A_584] :
      ( l1_pre_topc(B_583)
      | ~ m1_pre_topc(B_583,A_584)
      | ~ l1_pre_topc(A_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_114,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_106])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_153,plain,(
    ! [A_589,B_590] :
      ( r1_tarski(k1_tops_1(A_589,B_590),B_590)
      | ~ m1_subset_1(B_590,k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ l1_pre_topc(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_153])).

tff(c_158,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_155])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_175,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_40,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_597,A_598,C_599] :
      ( r1_tarski(B_597,k1_tops_1(A_598,C_599))
      | ~ r1_tarski(B_597,C_599)
      | ~ v3_pre_topc(B_597,A_598)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ l1_pre_topc(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_216,plain,(
    ! [B_597] :
      ( r1_tarski(B_597,k1_tops_1('#skF_4','#skF_6'))
      | ~ r1_tarski(B_597,'#skF_6')
      | ~ v3_pre_topc(B_597,'#skF_4')
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_214])).

tff(c_220,plain,(
    ! [B_600] :
      ( r1_tarski(B_600,k1_tops_1('#skF_4','#skF_6'))
      | ~ r1_tarski(B_600,'#skF_6')
      | ~ v3_pre_topc(B_600,'#skF_4')
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_216])).

tff(c_223,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_220])).

tff(c_226,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_223])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_226])).

tff(c_229,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_340,plain,(
    ! [C_611,A_612,B_613] :
      ( m1_connsp_2(C_611,A_612,B_613)
      | ~ r2_hidden(B_613,k1_tops_1(A_612,C_611))
      | ~ m1_subset_1(C_611,k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ m1_subset_1(B_613,u1_struct_0(A_612))
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_342,plain,(
    ! [B_613] :
      ( m1_connsp_2('#skF_6','#skF_4',B_613)
      | ~ r2_hidden(B_613,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_340])).

tff(c_344,plain,(
    ! [B_613] :
      ( m1_connsp_2('#skF_6','#skF_4',B_613)
      | ~ r2_hidden(B_613,'#skF_6')
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_114,c_46,c_342])).

tff(c_346,plain,(
    ! [B_614] :
      ( m1_connsp_2('#skF_6','#skF_4',B_614)
      | ~ r2_hidden(B_614,'#skF_6')
      | ~ m1_subset_1(B_614,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_344])).

tff(c_349,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_85,c_346])).

tff(c_352,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_349])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_274,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_383,plain,(
    ! [E_625,D_628,B_626,C_627,A_624] :
      ( k3_tmap_1(A_624,B_626,C_627,D_628,E_625) = k2_partfun1(u1_struct_0(C_627),u1_struct_0(B_626),E_625,u1_struct_0(D_628))
      | ~ m1_pre_topc(D_628,C_627)
      | ~ m1_subset_1(E_625,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627),u1_struct_0(B_626))))
      | ~ v1_funct_2(E_625,u1_struct_0(C_627),u1_struct_0(B_626))
      | ~ v1_funct_1(E_625)
      | ~ m1_pre_topc(D_628,A_624)
      | ~ m1_pre_topc(C_627,A_624)
      | ~ l1_pre_topc(B_626)
      | ~ v2_pre_topc(B_626)
      | v2_struct_0(B_626)
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_385,plain,(
    ! [A_624,D_628] :
      ( k3_tmap_1(A_624,'#skF_2','#skF_4',D_628,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_628))
      | ~ m1_pre_topc(D_628,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_628,A_624)
      | ~ m1_pre_topc('#skF_4',A_624)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(resolution,[status(thm)],[c_50,c_383])).

tff(c_388,plain,(
    ! [A_624,D_628] :
      ( k3_tmap_1(A_624,'#skF_2','#skF_4',D_628,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_628))
      | ~ m1_pre_topc(D_628,'#skF_4')
      | ~ m1_pre_topc(D_628,A_624)
      | ~ m1_pre_topc('#skF_4',A_624)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_385])).

tff(c_390,plain,(
    ! [A_629,D_630] :
      ( k3_tmap_1(A_629,'#skF_2','#skF_4',D_630,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_630))
      | ~ m1_pre_topc(D_630,'#skF_4')
      | ~ m1_pre_topc(D_630,A_629)
      | ~ m1_pre_topc('#skF_4',A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_388])).

tff(c_398,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_390])).

tff(c_412,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_48,c_398])).

tff(c_413,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_412])).

tff(c_367,plain,(
    ! [A_619,B_620,C_621,D_622] :
      ( k2_partfun1(u1_struct_0(A_619),u1_struct_0(B_620),C_621,u1_struct_0(D_622)) = k2_tmap_1(A_619,B_620,C_621,D_622)
      | ~ m1_pre_topc(D_622,A_619)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_619),u1_struct_0(B_620))))
      | ~ v1_funct_2(C_621,u1_struct_0(A_619),u1_struct_0(B_620))
      | ~ v1_funct_1(C_621)
      | ~ l1_pre_topc(B_620)
      | ~ v2_pre_topc(B_620)
      | v2_struct_0(B_620)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_369,plain,(
    ! [D_622] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_622)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_622)
      | ~ m1_pre_topc(D_622,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_367])).

tff(c_372,plain,(
    ! [D_622] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_622)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_622)
      | ~ m1_pre_topc(D_622,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_114,c_66,c_64,c_54,c_52,c_369])).

tff(c_373,plain,(
    ! [D_622] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_622)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_622)
      | ~ m1_pre_topc(D_622,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_372])).

tff(c_425,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_373])).

tff(c_432,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_425])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_275,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_83])).

tff(c_437,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_275])).

tff(c_713,plain,(
    ! [E_654,D_649,C_650,A_653,B_652,G_651] :
      ( r1_tmap_1(B_652,A_653,C_650,G_651)
      | ~ r1_tmap_1(D_649,A_653,k2_tmap_1(B_652,A_653,C_650,D_649),G_651)
      | ~ m1_connsp_2(E_654,B_652,G_651)
      | ~ r1_tarski(E_654,u1_struct_0(D_649))
      | ~ m1_subset_1(G_651,u1_struct_0(D_649))
      | ~ m1_subset_1(G_651,u1_struct_0(B_652))
      | ~ m1_subset_1(E_654,k1_zfmisc_1(u1_struct_0(B_652)))
      | ~ m1_pre_topc(D_649,B_652)
      | v2_struct_0(D_649)
      | ~ m1_subset_1(C_650,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_652),u1_struct_0(A_653))))
      | ~ v1_funct_2(C_650,u1_struct_0(B_652),u1_struct_0(A_653))
      | ~ v1_funct_1(C_650)
      | ~ l1_pre_topc(B_652)
      | ~ v2_pre_topc(B_652)
      | v2_struct_0(B_652)
      | ~ l1_pre_topc(A_653)
      | ~ v2_pre_topc(A_653)
      | v2_struct_0(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_715,plain,(
    ! [E_654] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_654,'#skF_4','#skF_8')
      | ~ r1_tarski(E_654,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_654,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_437,c_713])).

tff(c_718,plain,(
    ! [E_654] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_654,'#skF_4','#skF_8')
      | ~ r1_tarski(E_654,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_654,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_150,c_114,c_54,c_52,c_50,c_48,c_85,c_42,c_715])).

tff(c_720,plain,(
    ! [E_655] :
      ( ~ m1_connsp_2(E_655,'#skF_4','#skF_8')
      | ~ r1_tarski(E_655,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_655,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_62,c_274,c_718])).

tff(c_723,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_720])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_352,c_723])).

tff(c_729,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_24,plain,(
    ! [A_72] :
      ( m1_pre_topc(A_72,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_839,plain,(
    ! [E_677,D_680,B_678,A_676,C_679] :
      ( k3_tmap_1(A_676,B_678,C_679,D_680,E_677) = k2_partfun1(u1_struct_0(C_679),u1_struct_0(B_678),E_677,u1_struct_0(D_680))
      | ~ m1_pre_topc(D_680,C_679)
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_679),u1_struct_0(B_678))))
      | ~ v1_funct_2(E_677,u1_struct_0(C_679),u1_struct_0(B_678))
      | ~ v1_funct_1(E_677)
      | ~ m1_pre_topc(D_680,A_676)
      | ~ m1_pre_topc(C_679,A_676)
      | ~ l1_pre_topc(B_678)
      | ~ v2_pre_topc(B_678)
      | v2_struct_0(B_678)
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_841,plain,(
    ! [A_676,D_680] :
      ( k3_tmap_1(A_676,'#skF_2','#skF_4',D_680,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_680))
      | ~ m1_pre_topc(D_680,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_680,A_676)
      | ~ m1_pre_topc('#skF_4',A_676)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(resolution,[status(thm)],[c_50,c_839])).

tff(c_844,plain,(
    ! [A_676,D_680] :
      ( k3_tmap_1(A_676,'#skF_2','#skF_4',D_680,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_680))
      | ~ m1_pre_topc(D_680,'#skF_4')
      | ~ m1_pre_topc(D_680,A_676)
      | ~ m1_pre_topc('#skF_4',A_676)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_841])).

tff(c_846,plain,(
    ! [A_681,D_682] :
      ( k3_tmap_1(A_681,'#skF_2','#skF_4',D_682,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_682))
      | ~ m1_pre_topc(D_682,'#skF_4')
      | ~ m1_pre_topc(D_682,A_681)
      | ~ m1_pre_topc('#skF_4',A_681)
      | ~ l1_pre_topc(A_681)
      | ~ v2_pre_topc(A_681)
      | v2_struct_0(A_681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_844])).

tff(c_858,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_846])).

tff(c_876,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_858])).

tff(c_877,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_876])).

tff(c_924,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_927,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_924])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_927])).

tff(c_933,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_854,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_846])).

tff(c_868,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_48,c_854])).

tff(c_869,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_868])).

tff(c_823,plain,(
    ! [A_671,B_672,C_673,D_674] :
      ( k2_partfun1(u1_struct_0(A_671),u1_struct_0(B_672),C_673,u1_struct_0(D_674)) = k2_tmap_1(A_671,B_672,C_673,D_674)
      | ~ m1_pre_topc(D_674,A_671)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_671),u1_struct_0(B_672))))
      | ~ v1_funct_2(C_673,u1_struct_0(A_671),u1_struct_0(B_672))
      | ~ v1_funct_1(C_673)
      | ~ l1_pre_topc(B_672)
      | ~ v2_pre_topc(B_672)
      | v2_struct_0(B_672)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_825,plain,(
    ! [D_674] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_674)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_674)
      | ~ m1_pre_topc(D_674,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_823])).

tff(c_828,plain,(
    ! [D_674] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_674)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_674)
      | ~ m1_pre_topc(D_674,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_114,c_66,c_64,c_54,c_52,c_825])).

tff(c_829,plain,(
    ! [D_674] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_674)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_674)
      | ~ m1_pre_topc(D_674,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_828])).

tff(c_881,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_829])).

tff(c_888,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_881])).

tff(c_892,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_869])).

tff(c_856,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_846])).

tff(c_872,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_114,c_48,c_856])).

tff(c_873,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_872])).

tff(c_922,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_873])).

tff(c_923,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_923])).

tff(c_968,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_967,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_898,plain,(
    ! [D_687,C_688,A_686,B_683,E_685,G_684] :
      ( r1_tmap_1(D_687,B_683,k3_tmap_1(A_686,B_683,C_688,D_687,E_685),G_684)
      | ~ r1_tmap_1(C_688,B_683,E_685,G_684)
      | ~ m1_pre_topc(D_687,C_688)
      | ~ m1_subset_1(G_684,u1_struct_0(D_687))
      | ~ m1_subset_1(G_684,u1_struct_0(C_688))
      | ~ m1_subset_1(E_685,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_688),u1_struct_0(B_683))))
      | ~ v1_funct_2(E_685,u1_struct_0(C_688),u1_struct_0(B_683))
      | ~ v1_funct_1(E_685)
      | ~ m1_pre_topc(D_687,A_686)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc(C_688,A_686)
      | v2_struct_0(C_688)
      | ~ l1_pre_topc(B_683)
      | ~ v2_pre_topc(B_683)
      | v2_struct_0(B_683)
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_900,plain,(
    ! [D_687,A_686,G_684] :
      ( r1_tmap_1(D_687,'#skF_2',k3_tmap_1(A_686,'#skF_2','#skF_4',D_687,'#skF_5'),G_684)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_684)
      | ~ m1_pre_topc(D_687,'#skF_4')
      | ~ m1_subset_1(G_684,u1_struct_0(D_687))
      | ~ m1_subset_1(G_684,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_687,A_686)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc('#skF_4',A_686)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(resolution,[status(thm)],[c_50,c_898])).

tff(c_903,plain,(
    ! [D_687,A_686,G_684] :
      ( r1_tmap_1(D_687,'#skF_2',k3_tmap_1(A_686,'#skF_2','#skF_4',D_687,'#skF_5'),G_684)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_684)
      | ~ m1_pre_topc(D_687,'#skF_4')
      | ~ m1_subset_1(G_684,u1_struct_0(D_687))
      | ~ m1_subset_1(G_684,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_687,A_686)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc('#skF_4',A_686)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_900])).

tff(c_1179,plain,(
    ! [D_704,A_705,G_706] :
      ( r1_tmap_1(D_704,'#skF_2',k3_tmap_1(A_705,'#skF_2','#skF_4',D_704,'#skF_5'),G_706)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_706)
      | ~ m1_pre_topc(D_704,'#skF_4')
      | ~ m1_subset_1(G_706,u1_struct_0(D_704))
      | ~ m1_subset_1(G_706,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_704,A_705)
      | v2_struct_0(D_704)
      | ~ m1_pre_topc('#skF_4',A_705)
      | ~ l1_pre_topc(A_705)
      | ~ v2_pre_topc(A_705)
      | v2_struct_0(A_705) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_903])).

tff(c_1191,plain,(
    ! [G_706] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_706)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_706)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1(G_706,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_706,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1179])).

tff(c_1202,plain,(
    ! [G_706] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_706)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_706)
      | ~ m1_subset_1(G_706,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_706,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_114,c_968,c_48,c_48,c_1191])).

tff(c_1233,plain,(
    ! [G_710] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_710)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_710)
      | ~ m1_subset_1(G_710,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_710,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62,c_1202])).

tff(c_728,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_893,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_728])).

tff(c_1238,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1233,c_893])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_42,c_729,c_1238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:29:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.67  
% 4.07/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.67  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.07/1.67  
% 4.07/1.67  %Foreground sorts:
% 4.07/1.67  
% 4.07/1.67  
% 4.07/1.67  %Background operators:
% 4.07/1.67  
% 4.07/1.67  
% 4.07/1.67  %Foreground operators:
% 4.07/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.07/1.67  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.07/1.67  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.07/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.67  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.07/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.67  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.07/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.07/1.67  tff('#skF_7', type, '#skF_7': $i).
% 4.07/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.67  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.07/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.07/1.67  tff('#skF_6', type, '#skF_6': $i).
% 4.07/1.67  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.67  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.67  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.67  tff('#skF_8', type, '#skF_8': $i).
% 4.07/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.07/1.67  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.67  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.07/1.67  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.07/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.07/1.67  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.07/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.07/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.67  
% 4.20/1.70  tff(f_313, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.20/1.70  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.20/1.70  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.20/1.70  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.20/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.20/1.70  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.20/1.70  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.20/1.70  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.20/1.70  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.20/1.70  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.20/1.70  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.20/1.70  tff(f_255, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.20/1.70  tff(c_34, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 4.20/1.70  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_36, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_38, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_86, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 4.20/1.70  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_128, plain, (![B_587, A_588]: (v2_pre_topc(B_587) | ~m1_pre_topc(B_587, A_588) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.20/1.70  tff(c_140, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_128])).
% 4.20/1.70  tff(c_150, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_140])).
% 4.20/1.70  tff(c_94, plain, (![B_583, A_584]: (l1_pre_topc(B_583) | ~m1_pre_topc(B_583, A_584) | ~l1_pre_topc(A_584))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.20/1.70  tff(c_106, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_94])).
% 4.20/1.70  tff(c_114, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_106])).
% 4.20/1.70  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_153, plain, (![A_589, B_590]: (r1_tarski(k1_tops_1(A_589, B_590), B_590) | ~m1_subset_1(B_590, k1_zfmisc_1(u1_struct_0(A_589))) | ~l1_pre_topc(A_589))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.20/1.70  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_153])).
% 4.20/1.70  tff(c_158, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_155])).
% 4.20/1.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.70  tff(c_174, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_158, c_2])).
% 4.20/1.70  tff(c_175, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_174])).
% 4.20/1.70  tff(c_40, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.70  tff(c_214, plain, (![B_597, A_598, C_599]: (r1_tarski(B_597, k1_tops_1(A_598, C_599)) | ~r1_tarski(B_597, C_599) | ~v3_pre_topc(B_597, A_598) | ~m1_subset_1(C_599, k1_zfmisc_1(u1_struct_0(A_598))) | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0(A_598))) | ~l1_pre_topc(A_598))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.20/1.70  tff(c_216, plain, (![B_597]: (r1_tarski(B_597, k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski(B_597, '#skF_6') | ~v3_pre_topc(B_597, '#skF_4') | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_214])).
% 4.20/1.70  tff(c_220, plain, (![B_600]: (r1_tarski(B_600, k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski(B_600, '#skF_6') | ~v3_pre_topc(B_600, '#skF_4') | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_216])).
% 4.20/1.70  tff(c_223, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_220])).
% 4.20/1.70  tff(c_226, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_223])).
% 4.20/1.70  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_226])).
% 4.20/1.70  tff(c_229, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_174])).
% 4.20/1.70  tff(c_340, plain, (![C_611, A_612, B_613]: (m1_connsp_2(C_611, A_612, B_613) | ~r2_hidden(B_613, k1_tops_1(A_612, C_611)) | ~m1_subset_1(C_611, k1_zfmisc_1(u1_struct_0(A_612))) | ~m1_subset_1(B_613, u1_struct_0(A_612)) | ~l1_pre_topc(A_612) | ~v2_pre_topc(A_612) | v2_struct_0(A_612))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.20/1.70  tff(c_342, plain, (![B_613]: (m1_connsp_2('#skF_6', '#skF_4', B_613) | ~r2_hidden(B_613, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_613, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_340])).
% 4.20/1.70  tff(c_344, plain, (![B_613]: (m1_connsp_2('#skF_6', '#skF_4', B_613) | ~r2_hidden(B_613, '#skF_6') | ~m1_subset_1(B_613, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_114, c_46, c_342])).
% 4.20/1.70  tff(c_346, plain, (![B_614]: (m1_connsp_2('#skF_6', '#skF_4', B_614) | ~r2_hidden(B_614, '#skF_6') | ~m1_subset_1(B_614, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_344])).
% 4.20/1.70  tff(c_349, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_85, c_346])).
% 4.20/1.70  tff(c_352, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_349])).
% 4.20/1.70  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_76, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_84, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 4.20/1.70  tff(c_274, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 4.20/1.70  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_383, plain, (![E_625, D_628, B_626, C_627, A_624]: (k3_tmap_1(A_624, B_626, C_627, D_628, E_625)=k2_partfun1(u1_struct_0(C_627), u1_struct_0(B_626), E_625, u1_struct_0(D_628)) | ~m1_pre_topc(D_628, C_627) | ~m1_subset_1(E_625, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627), u1_struct_0(B_626)))) | ~v1_funct_2(E_625, u1_struct_0(C_627), u1_struct_0(B_626)) | ~v1_funct_1(E_625) | ~m1_pre_topc(D_628, A_624) | ~m1_pre_topc(C_627, A_624) | ~l1_pre_topc(B_626) | ~v2_pre_topc(B_626) | v2_struct_0(B_626) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.20/1.70  tff(c_385, plain, (![A_624, D_628]: (k3_tmap_1(A_624, '#skF_2', '#skF_4', D_628, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_628)) | ~m1_pre_topc(D_628, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_628, A_624) | ~m1_pre_topc('#skF_4', A_624) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(resolution, [status(thm)], [c_50, c_383])).
% 4.20/1.70  tff(c_388, plain, (![A_624, D_628]: (k3_tmap_1(A_624, '#skF_2', '#skF_4', D_628, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_628)) | ~m1_pre_topc(D_628, '#skF_4') | ~m1_pre_topc(D_628, A_624) | ~m1_pre_topc('#skF_4', A_624) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_385])).
% 4.20/1.70  tff(c_390, plain, (![A_629, D_630]: (k3_tmap_1(A_629, '#skF_2', '#skF_4', D_630, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_630)) | ~m1_pre_topc(D_630, '#skF_4') | ~m1_pre_topc(D_630, A_629) | ~m1_pre_topc('#skF_4', A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(negUnitSimplification, [status(thm)], [c_68, c_388])).
% 4.20/1.70  tff(c_398, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_390])).
% 4.20/1.70  tff(c_412, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_48, c_398])).
% 4.20/1.70  tff(c_413, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_412])).
% 4.20/1.70  tff(c_367, plain, (![A_619, B_620, C_621, D_622]: (k2_partfun1(u1_struct_0(A_619), u1_struct_0(B_620), C_621, u1_struct_0(D_622))=k2_tmap_1(A_619, B_620, C_621, D_622) | ~m1_pre_topc(D_622, A_619) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_619), u1_struct_0(B_620)))) | ~v1_funct_2(C_621, u1_struct_0(A_619), u1_struct_0(B_620)) | ~v1_funct_1(C_621) | ~l1_pre_topc(B_620) | ~v2_pre_topc(B_620) | v2_struct_0(B_620) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.20/1.70  tff(c_369, plain, (![D_622]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_622))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_622) | ~m1_pre_topc(D_622, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_367])).
% 4.20/1.70  tff(c_372, plain, (![D_622]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_622))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_622) | ~m1_pre_topc(D_622, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_114, c_66, c_64, c_54, c_52, c_369])).
% 4.20/1.70  tff(c_373, plain, (![D_622]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_622))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_622) | ~m1_pre_topc(D_622, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_372])).
% 4.20/1.70  tff(c_425, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_413, c_373])).
% 4.20/1.70  tff(c_432, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_425])).
% 4.20/1.70  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_313])).
% 4.20/1.70  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 4.20/1.70  tff(c_275, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_274, c_83])).
% 4.20/1.70  tff(c_437, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_275])).
% 4.20/1.70  tff(c_713, plain, (![E_654, D_649, C_650, A_653, B_652, G_651]: (r1_tmap_1(B_652, A_653, C_650, G_651) | ~r1_tmap_1(D_649, A_653, k2_tmap_1(B_652, A_653, C_650, D_649), G_651) | ~m1_connsp_2(E_654, B_652, G_651) | ~r1_tarski(E_654, u1_struct_0(D_649)) | ~m1_subset_1(G_651, u1_struct_0(D_649)) | ~m1_subset_1(G_651, u1_struct_0(B_652)) | ~m1_subset_1(E_654, k1_zfmisc_1(u1_struct_0(B_652))) | ~m1_pre_topc(D_649, B_652) | v2_struct_0(D_649) | ~m1_subset_1(C_650, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_652), u1_struct_0(A_653)))) | ~v1_funct_2(C_650, u1_struct_0(B_652), u1_struct_0(A_653)) | ~v1_funct_1(C_650) | ~l1_pre_topc(B_652) | ~v2_pre_topc(B_652) | v2_struct_0(B_652) | ~l1_pre_topc(A_653) | ~v2_pre_topc(A_653) | v2_struct_0(A_653))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.20/1.70  tff(c_715, plain, (![E_654]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_654, '#skF_4', '#skF_8') | ~r1_tarski(E_654, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_654, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_437, c_713])).
% 4.20/1.70  tff(c_718, plain, (![E_654]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_654, '#skF_4', '#skF_8') | ~r1_tarski(E_654, u1_struct_0('#skF_3')) | ~m1_subset_1(E_654, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_150, c_114, c_54, c_52, c_50, c_48, c_85, c_42, c_715])).
% 4.20/1.70  tff(c_720, plain, (![E_655]: (~m1_connsp_2(E_655, '#skF_4', '#skF_8') | ~r1_tarski(E_655, u1_struct_0('#skF_3')) | ~m1_subset_1(E_655, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_62, c_274, c_718])).
% 4.20/1.70  tff(c_723, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_720])).
% 4.20/1.70  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_352, c_723])).
% 4.20/1.70  tff(c_729, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.20/1.70  tff(c_24, plain, (![A_72]: (m1_pre_topc(A_72, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.20/1.70  tff(c_839, plain, (![E_677, D_680, B_678, A_676, C_679]: (k3_tmap_1(A_676, B_678, C_679, D_680, E_677)=k2_partfun1(u1_struct_0(C_679), u1_struct_0(B_678), E_677, u1_struct_0(D_680)) | ~m1_pre_topc(D_680, C_679) | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_679), u1_struct_0(B_678)))) | ~v1_funct_2(E_677, u1_struct_0(C_679), u1_struct_0(B_678)) | ~v1_funct_1(E_677) | ~m1_pre_topc(D_680, A_676) | ~m1_pre_topc(C_679, A_676) | ~l1_pre_topc(B_678) | ~v2_pre_topc(B_678) | v2_struct_0(B_678) | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.20/1.70  tff(c_841, plain, (![A_676, D_680]: (k3_tmap_1(A_676, '#skF_2', '#skF_4', D_680, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_680)) | ~m1_pre_topc(D_680, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_680, A_676) | ~m1_pre_topc('#skF_4', A_676) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(resolution, [status(thm)], [c_50, c_839])).
% 4.20/1.70  tff(c_844, plain, (![A_676, D_680]: (k3_tmap_1(A_676, '#skF_2', '#skF_4', D_680, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_680)) | ~m1_pre_topc(D_680, '#skF_4') | ~m1_pre_topc(D_680, A_676) | ~m1_pre_topc('#skF_4', A_676) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_841])).
% 4.20/1.70  tff(c_846, plain, (![A_681, D_682]: (k3_tmap_1(A_681, '#skF_2', '#skF_4', D_682, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_682)) | ~m1_pre_topc(D_682, '#skF_4') | ~m1_pre_topc(D_682, A_681) | ~m1_pre_topc('#skF_4', A_681) | ~l1_pre_topc(A_681) | ~v2_pre_topc(A_681) | v2_struct_0(A_681))), inference(negUnitSimplification, [status(thm)], [c_68, c_844])).
% 4.20/1.70  tff(c_858, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_846])).
% 4.20/1.70  tff(c_876, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_858])).
% 4.20/1.70  tff(c_877, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_876])).
% 4.20/1.70  tff(c_924, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_877])).
% 4.20/1.70  tff(c_927, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_924])).
% 4.20/1.70  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_927])).
% 4.20/1.70  tff(c_933, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_877])).
% 4.20/1.70  tff(c_854, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_846])).
% 4.20/1.70  tff(c_868, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_48, c_854])).
% 4.20/1.70  tff(c_869, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_868])).
% 4.20/1.70  tff(c_823, plain, (![A_671, B_672, C_673, D_674]: (k2_partfun1(u1_struct_0(A_671), u1_struct_0(B_672), C_673, u1_struct_0(D_674))=k2_tmap_1(A_671, B_672, C_673, D_674) | ~m1_pre_topc(D_674, A_671) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_671), u1_struct_0(B_672)))) | ~v1_funct_2(C_673, u1_struct_0(A_671), u1_struct_0(B_672)) | ~v1_funct_1(C_673) | ~l1_pre_topc(B_672) | ~v2_pre_topc(B_672) | v2_struct_0(B_672) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.20/1.70  tff(c_825, plain, (![D_674]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_674))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_674) | ~m1_pre_topc(D_674, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_823])).
% 4.20/1.70  tff(c_828, plain, (![D_674]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_674))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_674) | ~m1_pre_topc(D_674, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_114, c_66, c_64, c_54, c_52, c_825])).
% 4.20/1.70  tff(c_829, plain, (![D_674]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_674))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_674) | ~m1_pre_topc(D_674, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_828])).
% 4.20/1.70  tff(c_881, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_869, c_829])).
% 4.20/1.70  tff(c_888, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_881])).
% 4.20/1.70  tff(c_892, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_888, c_869])).
% 4.20/1.70  tff(c_856, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_846])).
% 4.20/1.70  tff(c_872, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_114, c_48, c_856])).
% 4.20/1.70  tff(c_873, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_872])).
% 4.20/1.70  tff(c_922, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_892, c_873])).
% 4.20/1.70  tff(c_923, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_922])).
% 4.20/1.70  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_933, c_923])).
% 4.20/1.70  tff(c_968, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_922])).
% 4.20/1.70  tff(c_967, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_922])).
% 4.20/1.70  tff(c_898, plain, (![D_687, C_688, A_686, B_683, E_685, G_684]: (r1_tmap_1(D_687, B_683, k3_tmap_1(A_686, B_683, C_688, D_687, E_685), G_684) | ~r1_tmap_1(C_688, B_683, E_685, G_684) | ~m1_pre_topc(D_687, C_688) | ~m1_subset_1(G_684, u1_struct_0(D_687)) | ~m1_subset_1(G_684, u1_struct_0(C_688)) | ~m1_subset_1(E_685, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_688), u1_struct_0(B_683)))) | ~v1_funct_2(E_685, u1_struct_0(C_688), u1_struct_0(B_683)) | ~v1_funct_1(E_685) | ~m1_pre_topc(D_687, A_686) | v2_struct_0(D_687) | ~m1_pre_topc(C_688, A_686) | v2_struct_0(C_688) | ~l1_pre_topc(B_683) | ~v2_pre_topc(B_683) | v2_struct_0(B_683) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.20/1.70  tff(c_900, plain, (![D_687, A_686, G_684]: (r1_tmap_1(D_687, '#skF_2', k3_tmap_1(A_686, '#skF_2', '#skF_4', D_687, '#skF_5'), G_684) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_684) | ~m1_pre_topc(D_687, '#skF_4') | ~m1_subset_1(G_684, u1_struct_0(D_687)) | ~m1_subset_1(G_684, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_687, A_686) | v2_struct_0(D_687) | ~m1_pre_topc('#skF_4', A_686) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(resolution, [status(thm)], [c_50, c_898])).
% 4.20/1.70  tff(c_903, plain, (![D_687, A_686, G_684]: (r1_tmap_1(D_687, '#skF_2', k3_tmap_1(A_686, '#skF_2', '#skF_4', D_687, '#skF_5'), G_684) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_684) | ~m1_pre_topc(D_687, '#skF_4') | ~m1_subset_1(G_684, u1_struct_0(D_687)) | ~m1_subset_1(G_684, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_687, A_686) | v2_struct_0(D_687) | ~m1_pre_topc('#skF_4', A_686) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_900])).
% 4.20/1.70  tff(c_1179, plain, (![D_704, A_705, G_706]: (r1_tmap_1(D_704, '#skF_2', k3_tmap_1(A_705, '#skF_2', '#skF_4', D_704, '#skF_5'), G_706) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_706) | ~m1_pre_topc(D_704, '#skF_4') | ~m1_subset_1(G_706, u1_struct_0(D_704)) | ~m1_subset_1(G_706, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_704, A_705) | v2_struct_0(D_704) | ~m1_pre_topc('#skF_4', A_705) | ~l1_pre_topc(A_705) | ~v2_pre_topc(A_705) | v2_struct_0(A_705))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_903])).
% 4.20/1.70  tff(c_1191, plain, (![G_706]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_706) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_706) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(G_706, u1_struct_0('#skF_3')) | ~m1_subset_1(G_706, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_967, c_1179])).
% 4.20/1.70  tff(c_1202, plain, (![G_706]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_706) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_706) | ~m1_subset_1(G_706, u1_struct_0('#skF_3')) | ~m1_subset_1(G_706, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_114, c_968, c_48, c_48, c_1191])).
% 4.20/1.70  tff(c_1233, plain, (![G_710]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_710) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_710) | ~m1_subset_1(G_710, u1_struct_0('#skF_3')) | ~m1_subset_1(G_710, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_62, c_1202])).
% 4.20/1.70  tff(c_728, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.20/1.70  tff(c_893, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_888, c_728])).
% 4.20/1.70  tff(c_1238, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1233, c_893])).
% 4.20/1.70  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_42, c_729, c_1238])).
% 4.20/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.70  
% 4.20/1.70  Inference rules
% 4.20/1.70  ----------------------
% 4.20/1.70  #Ref     : 0
% 4.20/1.70  #Sup     : 225
% 4.20/1.70  #Fact    : 0
% 4.20/1.70  #Define  : 0
% 4.20/1.70  #Split   : 10
% 4.20/1.70  #Chain   : 0
% 4.20/1.70  #Close   : 0
% 4.20/1.70  
% 4.20/1.70  Ordering : KBO
% 4.20/1.70  
% 4.20/1.70  Simplification rules
% 4.20/1.70  ----------------------
% 4.20/1.70  #Subsume      : 28
% 4.20/1.70  #Demod        : 470
% 4.20/1.70  #Tautology    : 137
% 4.20/1.70  #SimpNegUnit  : 62
% 4.20/1.70  #BackRed      : 9
% 4.20/1.70  
% 4.20/1.70  #Partial instantiations: 0
% 4.20/1.70  #Strategies tried      : 1
% 4.20/1.70  
% 4.20/1.70  Timing (in seconds)
% 4.20/1.70  ----------------------
% 4.20/1.70  Preprocessing        : 0.42
% 4.20/1.70  Parsing              : 0.20
% 4.20/1.70  CNF conversion       : 0.07
% 4.20/1.70  Main loop            : 0.46
% 4.20/1.70  Inferencing          : 0.15
% 4.20/1.70  Reduction            : 0.17
% 4.20/1.70  Demodulation         : 0.12
% 4.20/1.70  BG Simplification    : 0.03
% 4.20/1.70  Subsumption          : 0.09
% 4.20/1.70  Abstraction          : 0.02
% 4.20/1.70  MUC search           : 0.00
% 4.20/1.70  Cooper               : 0.00
% 4.20/1.70  Total                : 0.94
% 4.20/1.70  Index Insertion      : 0.00
% 4.20/1.70  Index Deletion       : 0.00
% 4.20/1.70  Index Matching       : 0.00
% 4.20/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
