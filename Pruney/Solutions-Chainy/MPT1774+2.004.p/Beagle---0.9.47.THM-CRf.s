%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 8.34s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 708 expanded)
%              Number of leaves         :   44 ( 279 expanded)
%              Depth                    :   16
%              Number of atoms          :  589 (5454 expanded)
%              Number of equality atoms :   34 ( 222 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_354,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_197,axiom,(
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

tff(f_165,axiom,(
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

tff(f_284,axiom,(
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

tff(f_237,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_48,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_56,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_99,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_70,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_116,plain,(
    ! [B_564,A_565] :
      ( l1_pre_topc(B_564)
      | ~ m1_pre_topc(B_564,A_565)
      | ~ l1_pre_topc(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_128,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_119])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_249,plain,(
    ! [C_585,A_586,B_587] :
      ( m1_subset_1(C_585,k1_zfmisc_1(u1_struct_0(A_586)))
      | ~ m1_subset_1(C_585,k1_zfmisc_1(u1_struct_0(B_587)))
      | ~ m1_pre_topc(B_587,A_586)
      | ~ l1_pre_topc(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_279,plain,(
    ! [A_594,A_595,B_596] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ m1_pre_topc(B_596,A_595)
      | ~ l1_pre_topc(A_595)
      | ~ r1_tarski(A_594,u1_struct_0(B_596)) ) ),
    inference(resolution,[status(thm)],[c_10,c_249])).

tff(c_285,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_62,c_279])).

tff(c_294,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_594,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_285])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_80,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_157,plain,(
    ! [B_568,A_569] :
      ( v2_pre_topc(B_568)
      | ~ m1_pre_topc(B_568,A_569)
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_169,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_160])).

tff(c_52,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_1684,plain,(
    ! [C_732,A_733,B_734,D_735] :
      ( m1_connsp_2(C_732,A_733,B_734)
      | ~ r2_hidden(B_734,D_735)
      | ~ r1_tarski(D_735,C_732)
      | ~ v3_pre_topc(D_735,A_733)
      | ~ m1_subset_1(D_735,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_subset_1(C_732,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_subset_1(B_734,u1_struct_0(A_733))
      | ~ l1_pre_topc(A_733)
      | ~ v2_pre_topc(A_733)
      | v2_struct_0(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1890,plain,(
    ! [C_763,A_764] :
      ( m1_connsp_2(C_763,A_764,'#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ v3_pre_topc('#skF_7',A_764)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_764)))
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0(A_764)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_764))
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(resolution,[status(thm)],[c_52,c_1684])).

tff(c_1905,plain,(
    ! [C_763] :
      ( m1_connsp_2(C_763,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_294,c_1890])).

tff(c_1929,plain,(
    ! [C_763] :
      ( m1_connsp_2(C_763,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_169,c_128,c_58,c_1905])).

tff(c_1930,plain,(
    ! [C_763] :
      ( m1_connsp_2(C_763,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1929])).

tff(c_2607,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1930])).

tff(c_350,plain,(
    ! [A_602] :
      ( m1_subset_1(A_602,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_602,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_285])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_360,plain,(
    ! [A_602] :
      ( r1_tarski(A_602,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_602,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_350,c_8])).

tff(c_283,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_279])).

tff(c_298,plain,(
    ! [A_597] :
      ( m1_subset_1(A_597,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_597,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_283])).

tff(c_309,plain,(
    ! [A_598] :
      ( r1_tarski(A_598,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_598,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_298,c_8])).

tff(c_321,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_309])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_106,plain,(
    ! [A_560,B_561] :
      ( r1_tarski(A_560,B_561)
      | ~ m1_subset_1(A_560,k1_zfmisc_1(B_561)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_179,plain,(
    ! [A_570,C_571,B_572] :
      ( m1_subset_1(A_570,C_571)
      | ~ m1_subset_1(B_572,k1_zfmisc_1(C_571))
      | ~ r2_hidden(A_570,B_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    ! [A_574,B_575,A_576] :
      ( m1_subset_1(A_574,B_575)
      | ~ r2_hidden(A_574,A_576)
      | ~ r1_tarski(A_576,B_575) ) ),
    inference(resolution,[status(thm)],[c_10,c_179])).

tff(c_194,plain,(
    ! [B_577] :
      ( m1_subset_1('#skF_8',B_577)
      | ~ r1_tarski('#skF_7',B_577) ) ),
    inference(resolution,[status(thm)],[c_52,c_190])).

tff(c_205,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_194])).

tff(c_54,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_74,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_287,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_74,c_279])).

tff(c_297,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_594,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_287])).

tff(c_1902,plain,(
    ! [C_763] :
      ( m1_connsp_2(C_763,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ v3_pre_topc('#skF_7','#skF_3')
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_297,c_1890])).

tff(c_1925,plain,(
    ! [C_763] :
      ( m1_connsp_2(C_763,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_763)
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80,c_78,c_205,c_54,c_1902])).

tff(c_1941,plain,(
    ! [C_765] :
      ( m1_connsp_2(C_765,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_765)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1925])).

tff(c_2124,plain,(
    ! [A_773] :
      ( m1_connsp_2(A_773,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',A_773)
      | ~ r1_tarski(A_773,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1941])).

tff(c_2196,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_321,c_2124])).

tff(c_2251,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2196])).

tff(c_2268,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_360,c_2251])).

tff(c_2278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2268])).

tff(c_2280,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2196])).

tff(c_493,plain,(
    ! [D_623,C_624,A_625] :
      ( v3_pre_topc(D_623,C_624)
      | ~ m1_subset_1(D_623,k1_zfmisc_1(u1_struct_0(C_624)))
      | ~ v3_pre_topc(D_623,A_625)
      | ~ m1_pre_topc(C_624,A_625)
      | ~ m1_subset_1(D_623,k1_zfmisc_1(u1_struct_0(A_625)))
      | ~ l1_pre_topc(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2734,plain,(
    ! [A_809,C_810,A_811] :
      ( v3_pre_topc(A_809,C_810)
      | ~ v3_pre_topc(A_809,A_811)
      | ~ m1_pre_topc(C_810,A_811)
      | ~ m1_subset_1(A_809,k1_zfmisc_1(u1_struct_0(A_811)))
      | ~ l1_pre_topc(A_811)
      | ~ r1_tarski(A_809,u1_struct_0(C_810)) ) ),
    inference(resolution,[status(thm)],[c_10,c_493])).

tff(c_2738,plain,(
    ! [A_809] :
      ( v3_pre_topc(A_809,'#skF_5')
      | ~ v3_pre_topc(A_809,'#skF_3')
      | ~ m1_subset_1(A_809,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_809,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_2734])).

tff(c_2753,plain,(
    ! [A_812] :
      ( v3_pre_topc(A_812,'#skF_5')
      | ~ v3_pre_topc(A_812,'#skF_3')
      | ~ m1_subset_1(A_812,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_812,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2738])).

tff(c_2807,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_2753])).

tff(c_2844,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_54,c_2807])).

tff(c_2846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2607,c_2844])).

tff(c_2849,plain,(
    ! [C_813] :
      ( m1_connsp_2(C_813,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_813)
      | ~ m1_subset_1(C_813,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_1930])).

tff(c_2918,plain,(
    ! [A_814] :
      ( m1_connsp_2(A_814,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',A_814)
      | ~ r1_tarski(A_814,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_294,c_2849])).

tff(c_2961,plain,
    ( m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_2918])).

tff(c_2992,plain,(
    m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2961])).

tff(c_24,plain,(
    ! [C_46,A_43,B_44] :
      ( m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_connsp_2(C_46,A_43,B_44)
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3000,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2992,c_24])).

tff(c_3003,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_128,c_58,c_3000])).

tff(c_3004,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3003])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_96,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_97,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_178,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_98,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_248,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_98])).

tff(c_86,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_84,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_66,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_2111,plain,(
    ! [D_771,A_768,E_767,C_770,B_769] :
      ( k3_tmap_1(A_768,B_769,C_770,D_771,E_767) = k2_partfun1(u1_struct_0(C_770),u1_struct_0(B_769),E_767,u1_struct_0(D_771))
      | ~ m1_pre_topc(D_771,C_770)
      | ~ m1_subset_1(E_767,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_770),u1_struct_0(B_769))))
      | ~ v1_funct_2(E_767,u1_struct_0(C_770),u1_struct_0(B_769))
      | ~ v1_funct_1(E_767)
      | ~ m1_pre_topc(D_771,A_768)
      | ~ m1_pre_topc(C_770,A_768)
      | ~ l1_pre_topc(B_769)
      | ~ v2_pre_topc(B_769)
      | v2_struct_0(B_769)
      | ~ l1_pre_topc(A_768)
      | ~ v2_pre_topc(A_768)
      | v2_struct_0(A_768) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2113,plain,(
    ! [A_768,D_771] :
      ( k3_tmap_1(A_768,'#skF_2','#skF_5',D_771,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_771))
      | ~ m1_pre_topc(D_771,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_771,A_768)
      | ~ m1_pre_topc('#skF_5',A_768)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_768)
      | ~ v2_pre_topc(A_768)
      | v2_struct_0(A_768) ) ),
    inference(resolution,[status(thm)],[c_64,c_2111])).

tff(c_2119,plain,(
    ! [A_768,D_771] :
      ( k3_tmap_1(A_768,'#skF_2','#skF_5',D_771,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_771))
      | ~ m1_pre_topc(D_771,'#skF_5')
      | ~ m1_pre_topc(D_771,A_768)
      | ~ m1_pre_topc('#skF_5',A_768)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_768)
      | ~ v2_pre_topc(A_768)
      | v2_struct_0(A_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_68,c_66,c_2113])).

tff(c_4719,plain,(
    ! [A_876,D_877] :
      ( k3_tmap_1(A_876,'#skF_2','#skF_5',D_877,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_877))
      | ~ m1_pre_topc(D_877,'#skF_5')
      | ~ m1_pre_topc(D_877,A_876)
      | ~ m1_pre_topc('#skF_5',A_876)
      | ~ l1_pre_topc(A_876)
      | ~ v2_pre_topc(A_876)
      | v2_struct_0(A_876) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2119])).

tff(c_4727,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4719])).

tff(c_4739,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_70,c_62,c_4727])).

tff(c_4740,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4739])).

tff(c_1828,plain,(
    ! [A_752,B_753,C_754,D_755] :
      ( k2_partfun1(u1_struct_0(A_752),u1_struct_0(B_753),C_754,u1_struct_0(D_755)) = k2_tmap_1(A_752,B_753,C_754,D_755)
      | ~ m1_pre_topc(D_755,A_752)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_752),u1_struct_0(B_753))))
      | ~ v1_funct_2(C_754,u1_struct_0(A_752),u1_struct_0(B_753))
      | ~ v1_funct_1(C_754)
      | ~ l1_pre_topc(B_753)
      | ~ v2_pre_topc(B_753)
      | v2_struct_0(B_753)
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1830,plain,(
    ! [D_755] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_755)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_755)
      | ~ m1_pre_topc(D_755,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1828])).

tff(c_1836,plain,(
    ! [D_755] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_755)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_755)
      | ~ m1_pre_topc(D_755,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_128,c_86,c_84,c_68,c_66,c_1830])).

tff(c_1837,plain,(
    ! [D_755] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_755)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_755)
      | ~ m1_pre_topc(D_755,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_88,c_1836])).

tff(c_4744,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4740,c_1837])).

tff(c_4751,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4744])).

tff(c_4756,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_178])).

tff(c_42,plain,(
    ! [A_178,C_274,G_304,D_290,E_298,B_242] :
      ( r1_tmap_1(B_242,A_178,C_274,G_304)
      | ~ r1_tmap_1(D_290,A_178,k2_tmap_1(B_242,A_178,C_274,D_290),G_304)
      | ~ m1_connsp_2(E_298,B_242,G_304)
      | ~ r1_tarski(E_298,u1_struct_0(D_290))
      | ~ m1_subset_1(G_304,u1_struct_0(D_290))
      | ~ m1_subset_1(G_304,u1_struct_0(B_242))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0(B_242)))
      | ~ m1_pre_topc(D_290,B_242)
      | v2_struct_0(D_290)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_242),u1_struct_0(A_178))))
      | ~ v1_funct_2(C_274,u1_struct_0(B_242),u1_struct_0(A_178))
      | ~ v1_funct_1(C_274)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_4762,plain,(
    ! [E_298] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_298,'#skF_5','#skF_8')
      | ~ r1_tarski(E_298,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4756,c_42])).

tff(c_4765,plain,(
    ! [E_298] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_298,'#skF_5','#skF_8')
      | ~ r1_tarski(E_298,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_169,c_128,c_68,c_66,c_64,c_62,c_58,c_99,c_4762])).

tff(c_4767,plain,(
    ! [E_878] :
      ( ~ m1_connsp_2(E_878,'#skF_5','#skF_8')
      | ~ r1_tarski(E_878,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_878,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_72,c_76,c_248,c_4765])).

tff(c_4785,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8')
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3004,c_4767])).

tff(c_4843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2992,c_4785])).

tff(c_4844,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_7089,plain,(
    ! [D_1090,F_1092,B_1091,A_1093,C_1089] :
      ( r1_tmap_1(D_1090,A_1093,k2_tmap_1(B_1091,A_1093,C_1089,D_1090),F_1092)
      | ~ r1_tmap_1(B_1091,A_1093,C_1089,F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0(D_1090))
      | ~ m1_subset_1(F_1092,u1_struct_0(B_1091))
      | ~ m1_pre_topc(D_1090,B_1091)
      | v2_struct_0(D_1090)
      | ~ m1_subset_1(C_1089,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1091),u1_struct_0(A_1093))))
      | ~ v1_funct_2(C_1089,u1_struct_0(B_1091),u1_struct_0(A_1093))
      | ~ v1_funct_1(C_1089)
      | ~ l1_pre_topc(B_1091)
      | ~ v2_pre_topc(B_1091)
      | v2_struct_0(B_1091)
      | ~ l1_pre_topc(A_1093)
      | ~ v2_pre_topc(A_1093)
      | v2_struct_0(A_1093) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_7091,plain,(
    ! [D_1090,F_1092] :
      ( r1_tmap_1(D_1090,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1090),F_1092)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0(D_1090))
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1090,'#skF_5')
      | v2_struct_0(D_1090)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_7089])).

tff(c_7097,plain,(
    ! [D_1090,F_1092] :
      ( r1_tmap_1(D_1090,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1090),F_1092)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0(D_1090))
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1090,'#skF_5')
      | v2_struct_0(D_1090)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_169,c_128,c_68,c_66,c_7091])).

tff(c_7098,plain,(
    ! [D_1090,F_1092] :
      ( r1_tmap_1(D_1090,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1090),F_1092)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0(D_1090))
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1090,'#skF_5')
      | v2_struct_0(D_1090) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_72,c_7097])).

tff(c_6757,plain,(
    ! [B_1075,A_1074,C_1076,D_1077,E_1073] :
      ( k3_tmap_1(A_1074,B_1075,C_1076,D_1077,E_1073) = k2_partfun1(u1_struct_0(C_1076),u1_struct_0(B_1075),E_1073,u1_struct_0(D_1077))
      | ~ m1_pre_topc(D_1077,C_1076)
      | ~ m1_subset_1(E_1073,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1076),u1_struct_0(B_1075))))
      | ~ v1_funct_2(E_1073,u1_struct_0(C_1076),u1_struct_0(B_1075))
      | ~ v1_funct_1(E_1073)
      | ~ m1_pre_topc(D_1077,A_1074)
      | ~ m1_pre_topc(C_1076,A_1074)
      | ~ l1_pre_topc(B_1075)
      | ~ v2_pre_topc(B_1075)
      | v2_struct_0(B_1075)
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074)
      | v2_struct_0(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6759,plain,(
    ! [A_1074,D_1077] :
      ( k3_tmap_1(A_1074,'#skF_2','#skF_5',D_1077,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1077))
      | ~ m1_pre_topc(D_1077,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_1077,A_1074)
      | ~ m1_pre_topc('#skF_5',A_1074)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074)
      | v2_struct_0(A_1074) ) ),
    inference(resolution,[status(thm)],[c_64,c_6757])).

tff(c_6765,plain,(
    ! [A_1074,D_1077] :
      ( k3_tmap_1(A_1074,'#skF_2','#skF_5',D_1077,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1077))
      | ~ m1_pre_topc(D_1077,'#skF_5')
      | ~ m1_pre_topc(D_1077,A_1074)
      | ~ m1_pre_topc('#skF_5',A_1074)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074)
      | v2_struct_0(A_1074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_68,c_66,c_6759])).

tff(c_9365,plain,(
    ! [A_1182,D_1183] :
      ( k3_tmap_1(A_1182,'#skF_2','#skF_5',D_1183,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1183))
      | ~ m1_pre_topc(D_1183,'#skF_5')
      | ~ m1_pre_topc(D_1183,A_1182)
      | ~ m1_pre_topc('#skF_5',A_1182)
      | ~ l1_pre_topc(A_1182)
      | ~ v2_pre_topc(A_1182)
      | v2_struct_0(A_1182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6765])).

tff(c_9373,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_9365])).

tff(c_9385,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_70,c_62,c_9373])).

tff(c_9386,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9385])).

tff(c_6494,plain,(
    ! [A_1060,B_1061,C_1062,D_1063] :
      ( k2_partfun1(u1_struct_0(A_1060),u1_struct_0(B_1061),C_1062,u1_struct_0(D_1063)) = k2_tmap_1(A_1060,B_1061,C_1062,D_1063)
      | ~ m1_pre_topc(D_1063,A_1060)
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1060),u1_struct_0(B_1061))))
      | ~ v1_funct_2(C_1062,u1_struct_0(A_1060),u1_struct_0(B_1061))
      | ~ v1_funct_1(C_1062)
      | ~ l1_pre_topc(B_1061)
      | ~ v2_pre_topc(B_1061)
      | v2_struct_0(B_1061)
      | ~ l1_pre_topc(A_1060)
      | ~ v2_pre_topc(A_1060)
      | v2_struct_0(A_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6496,plain,(
    ! [D_1063] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1063)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1063)
      | ~ m1_pre_topc(D_1063,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_6494])).

tff(c_6502,plain,(
    ! [D_1063] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1063)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1063)
      | ~ m1_pre_topc(D_1063,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_128,c_86,c_84,c_68,c_66,c_6496])).

tff(c_6503,plain,(
    ! [D_1063] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1063)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1063)
      | ~ m1_pre_topc(D_1063,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_88,c_6502])).

tff(c_9390,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9386,c_6503])).

tff(c_9397,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9390])).

tff(c_4845,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_9402,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9397,c_4845])).

tff(c_9409,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7098,c_9402])).

tff(c_9412,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_99,c_4844,c_9409])).

tff(c_9414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:42:11 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.34/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.00  
% 8.55/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.00  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 8.55/3.00  
% 8.55/3.00  %Foreground sorts:
% 8.55/3.00  
% 8.55/3.00  
% 8.55/3.00  %Background operators:
% 8.55/3.00  
% 8.55/3.00  
% 8.55/3.00  %Foreground operators:
% 8.55/3.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.55/3.00  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 8.55/3.00  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.55/3.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.55/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.55/3.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.55/3.00  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.55/3.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.55/3.00  tff('#skF_7', type, '#skF_7': $i).
% 8.55/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.55/3.00  tff('#skF_5', type, '#skF_5': $i).
% 8.55/3.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.55/3.00  tff('#skF_6', type, '#skF_6': $i).
% 8.55/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.55/3.00  tff('#skF_3', type, '#skF_3': $i).
% 8.55/3.00  tff('#skF_9', type, '#skF_9': $i).
% 8.55/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.55/3.00  tff('#skF_8', type, '#skF_8': $i).
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/3.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.55/3.00  tff('#skF_4', type, '#skF_4': $i).
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/3.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.55/3.00  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.55/3.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.55/3.00  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.55/3.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.55/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.55/3.00  
% 8.55/3.03  tff(f_354, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 8.55/3.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.55/3.03  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.55/3.03  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.55/3.03  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 8.55/3.03  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.55/3.03  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 8.55/3.03  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.55/3.03  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 8.55/3.03  tff(f_114, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 8.55/3.03  tff(f_197, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 8.55/3.03  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.55/3.03  tff(f_284, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 8.55/3.03  tff(f_237, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 8.55/3.03  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_58, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_48, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_56, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_99, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 8.55/3.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/3.03  tff(c_50, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_70, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_116, plain, (![B_564, A_565]: (l1_pre_topc(B_564) | ~m1_pre_topc(B_564, A_565) | ~l1_pre_topc(A_565))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.55/3.03  tff(c_119, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_116])).
% 8.55/3.03  tff(c_128, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_119])).
% 8.55/3.03  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.55/3.03  tff(c_249, plain, (![C_585, A_586, B_587]: (m1_subset_1(C_585, k1_zfmisc_1(u1_struct_0(A_586))) | ~m1_subset_1(C_585, k1_zfmisc_1(u1_struct_0(B_587))) | ~m1_pre_topc(B_587, A_586) | ~l1_pre_topc(A_586))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/3.03  tff(c_279, plain, (![A_594, A_595, B_596]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0(A_595))) | ~m1_pre_topc(B_596, A_595) | ~l1_pre_topc(A_595) | ~r1_tarski(A_594, u1_struct_0(B_596)))), inference(resolution, [status(thm)], [c_10, c_249])).
% 8.55/3.03  tff(c_285, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_594, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_62, c_279])).
% 8.55/3.03  tff(c_294, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_594, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_285])).
% 8.55/3.03  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_80, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_157, plain, (![B_568, A_569]: (v2_pre_topc(B_568) | ~m1_pre_topc(B_568, A_569) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.55/3.03  tff(c_160, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_157])).
% 8.55/3.03  tff(c_169, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_160])).
% 8.55/3.03  tff(c_52, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_1684, plain, (![C_732, A_733, B_734, D_735]: (m1_connsp_2(C_732, A_733, B_734) | ~r2_hidden(B_734, D_735) | ~r1_tarski(D_735, C_732) | ~v3_pre_topc(D_735, A_733) | ~m1_subset_1(D_735, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_subset_1(C_732, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_subset_1(B_734, u1_struct_0(A_733)) | ~l1_pre_topc(A_733) | ~v2_pre_topc(A_733) | v2_struct_0(A_733))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.55/3.03  tff(c_1890, plain, (![C_763, A_764]: (m1_connsp_2(C_763, A_764, '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~v3_pre_topc('#skF_7', A_764) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_764))) | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0(A_764))) | ~m1_subset_1('#skF_8', u1_struct_0(A_764)) | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(resolution, [status(thm)], [c_52, c_1684])).
% 8.55/3.03  tff(c_1905, plain, (![C_763]: (m1_connsp_2(C_763, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_294, c_1890])).
% 8.55/3.03  tff(c_1929, plain, (![C_763]: (m1_connsp_2(C_763, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_169, c_128, c_58, c_1905])).
% 8.55/3.03  tff(c_1930, plain, (![C_763]: (m1_connsp_2(C_763, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_1929])).
% 8.55/3.03  tff(c_2607, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_1930])).
% 8.55/3.03  tff(c_350, plain, (![A_602]: (m1_subset_1(A_602, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_602, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_285])).
% 8.55/3.03  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.55/3.03  tff(c_360, plain, (![A_602]: (r1_tarski(A_602, u1_struct_0('#skF_5')) | ~r1_tarski(A_602, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_350, c_8])).
% 8.55/3.03  tff(c_283, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_594, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_279])).
% 8.55/3.03  tff(c_298, plain, (![A_597]: (m1_subset_1(A_597, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_597, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_283])).
% 8.55/3.03  tff(c_309, plain, (![A_598]: (r1_tarski(A_598, u1_struct_0('#skF_3')) | ~r1_tarski(A_598, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_298, c_8])).
% 8.55/3.03  tff(c_321, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_309])).
% 8.55/3.03  tff(c_82, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_106, plain, (![A_560, B_561]: (r1_tarski(A_560, B_561) | ~m1_subset_1(A_560, k1_zfmisc_1(B_561)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.55/3.03  tff(c_110, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_106])).
% 8.55/3.03  tff(c_179, plain, (![A_570, C_571, B_572]: (m1_subset_1(A_570, C_571) | ~m1_subset_1(B_572, k1_zfmisc_1(C_571)) | ~r2_hidden(A_570, B_572))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/3.03  tff(c_190, plain, (![A_574, B_575, A_576]: (m1_subset_1(A_574, B_575) | ~r2_hidden(A_574, A_576) | ~r1_tarski(A_576, B_575))), inference(resolution, [status(thm)], [c_10, c_179])).
% 8.55/3.03  tff(c_194, plain, (![B_577]: (m1_subset_1('#skF_8', B_577) | ~r1_tarski('#skF_7', B_577))), inference(resolution, [status(thm)], [c_52, c_190])).
% 8.55/3.03  tff(c_205, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_110, c_194])).
% 8.55/3.03  tff(c_54, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_74, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_287, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_594, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_74, c_279])).
% 8.55/3.03  tff(c_297, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_594, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_287])).
% 8.55/3.03  tff(c_1902, plain, (![C_763]: (m1_connsp_2(C_763, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~v3_pre_topc('#skF_7', '#skF_3') | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_297, c_1890])).
% 8.55/3.03  tff(c_1925, plain, (![C_763]: (m1_connsp_2(C_763, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_763) | ~m1_subset_1(C_763, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80, c_78, c_205, c_54, c_1902])).
% 8.55/3.03  tff(c_1941, plain, (![C_765]: (m1_connsp_2(C_765, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_765) | ~m1_subset_1(C_765, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_82, c_1925])).
% 8.55/3.03  tff(c_2124, plain, (![A_773]: (m1_connsp_2(A_773, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', A_773) | ~r1_tarski(A_773, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_1941])).
% 8.55/3.03  tff(c_2196, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_321, c_2124])).
% 8.55/3.03  tff(c_2251, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_2196])).
% 8.55/3.03  tff(c_2268, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_360, c_2251])).
% 8.55/3.03  tff(c_2278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2268])).
% 8.55/3.03  tff(c_2280, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2196])).
% 8.55/3.03  tff(c_493, plain, (![D_623, C_624, A_625]: (v3_pre_topc(D_623, C_624) | ~m1_subset_1(D_623, k1_zfmisc_1(u1_struct_0(C_624))) | ~v3_pre_topc(D_623, A_625) | ~m1_pre_topc(C_624, A_625) | ~m1_subset_1(D_623, k1_zfmisc_1(u1_struct_0(A_625))) | ~l1_pre_topc(A_625))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.55/3.03  tff(c_2734, plain, (![A_809, C_810, A_811]: (v3_pre_topc(A_809, C_810) | ~v3_pre_topc(A_809, A_811) | ~m1_pre_topc(C_810, A_811) | ~m1_subset_1(A_809, k1_zfmisc_1(u1_struct_0(A_811))) | ~l1_pre_topc(A_811) | ~r1_tarski(A_809, u1_struct_0(C_810)))), inference(resolution, [status(thm)], [c_10, c_493])).
% 8.55/3.03  tff(c_2738, plain, (![A_809]: (v3_pre_topc(A_809, '#skF_5') | ~v3_pre_topc(A_809, '#skF_3') | ~m1_subset_1(A_809, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_809, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_2734])).
% 8.55/3.03  tff(c_2753, plain, (![A_812]: (v3_pre_topc(A_812, '#skF_5') | ~v3_pre_topc(A_812, '#skF_3') | ~m1_subset_1(A_812, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_812, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2738])).
% 8.55/3.03  tff(c_2807, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_2753])).
% 8.55/3.03  tff(c_2844, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_54, c_2807])).
% 8.55/3.03  tff(c_2846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2607, c_2844])).
% 8.55/3.03  tff(c_2849, plain, (![C_813]: (m1_connsp_2(C_813, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_813) | ~m1_subset_1(C_813, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_1930])).
% 8.55/3.03  tff(c_2918, plain, (![A_814]: (m1_connsp_2(A_814, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', A_814) | ~r1_tarski(A_814, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_294, c_2849])).
% 8.55/3.03  tff(c_2961, plain, (m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_2918])).
% 8.55/3.03  tff(c_2992, plain, (m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2961])).
% 8.55/3.03  tff(c_24, plain, (![C_46, A_43, B_44]: (m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_connsp_2(C_46, A_43, B_44) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.55/3.03  tff(c_3000, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2992, c_24])).
% 8.55/3.03  tff(c_3003, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_128, c_58, c_3000])).
% 8.55/3.03  tff(c_3004, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_3003])).
% 8.55/3.03  tff(c_88, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_96, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_97, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_96])).
% 8.55/3.03  tff(c_178, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_97])).
% 8.55/3.03  tff(c_90, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_98, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_90])).
% 8.55/3.03  tff(c_248, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_98])).
% 8.55/3.03  tff(c_86, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_84, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_66, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_354])).
% 8.55/3.03  tff(c_2111, plain, (![D_771, A_768, E_767, C_770, B_769]: (k3_tmap_1(A_768, B_769, C_770, D_771, E_767)=k2_partfun1(u1_struct_0(C_770), u1_struct_0(B_769), E_767, u1_struct_0(D_771)) | ~m1_pre_topc(D_771, C_770) | ~m1_subset_1(E_767, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_770), u1_struct_0(B_769)))) | ~v1_funct_2(E_767, u1_struct_0(C_770), u1_struct_0(B_769)) | ~v1_funct_1(E_767) | ~m1_pre_topc(D_771, A_768) | ~m1_pre_topc(C_770, A_768) | ~l1_pre_topc(B_769) | ~v2_pre_topc(B_769) | v2_struct_0(B_769) | ~l1_pre_topc(A_768) | ~v2_pre_topc(A_768) | v2_struct_0(A_768))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.55/3.03  tff(c_2113, plain, (![A_768, D_771]: (k3_tmap_1(A_768, '#skF_2', '#skF_5', D_771, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_771)) | ~m1_pre_topc(D_771, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_771, A_768) | ~m1_pre_topc('#skF_5', A_768) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_768) | ~v2_pre_topc(A_768) | v2_struct_0(A_768))), inference(resolution, [status(thm)], [c_64, c_2111])).
% 8.55/3.03  tff(c_2119, plain, (![A_768, D_771]: (k3_tmap_1(A_768, '#skF_2', '#skF_5', D_771, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_771)) | ~m1_pre_topc(D_771, '#skF_5') | ~m1_pre_topc(D_771, A_768) | ~m1_pre_topc('#skF_5', A_768) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_768) | ~v2_pre_topc(A_768) | v2_struct_0(A_768))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_68, c_66, c_2113])).
% 8.55/3.03  tff(c_4719, plain, (![A_876, D_877]: (k3_tmap_1(A_876, '#skF_2', '#skF_5', D_877, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_877)) | ~m1_pre_topc(D_877, '#skF_5') | ~m1_pre_topc(D_877, A_876) | ~m1_pre_topc('#skF_5', A_876) | ~l1_pre_topc(A_876) | ~v2_pre_topc(A_876) | v2_struct_0(A_876))), inference(negUnitSimplification, [status(thm)], [c_88, c_2119])).
% 8.55/3.03  tff(c_4727, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_4719])).
% 8.55/3.03  tff(c_4739, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_70, c_62, c_4727])).
% 8.55/3.03  tff(c_4740, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_82, c_4739])).
% 8.55/3.03  tff(c_1828, plain, (![A_752, B_753, C_754, D_755]: (k2_partfun1(u1_struct_0(A_752), u1_struct_0(B_753), C_754, u1_struct_0(D_755))=k2_tmap_1(A_752, B_753, C_754, D_755) | ~m1_pre_topc(D_755, A_752) | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_752), u1_struct_0(B_753)))) | ~v1_funct_2(C_754, u1_struct_0(A_752), u1_struct_0(B_753)) | ~v1_funct_1(C_754) | ~l1_pre_topc(B_753) | ~v2_pre_topc(B_753) | v2_struct_0(B_753) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.55/3.03  tff(c_1830, plain, (![D_755]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_755))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_755) | ~m1_pre_topc(D_755, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1828])).
% 8.55/3.03  tff(c_1836, plain, (![D_755]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_755))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_755) | ~m1_pre_topc(D_755, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_128, c_86, c_84, c_68, c_66, c_1830])).
% 8.55/3.03  tff(c_1837, plain, (![D_755]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_755))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_755) | ~m1_pre_topc(D_755, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_88, c_1836])).
% 8.55/3.03  tff(c_4744, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4740, c_1837])).
% 8.55/3.03  tff(c_4751, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4744])).
% 8.55/3.03  tff(c_4756, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_178])).
% 8.55/3.03  tff(c_42, plain, (![A_178, C_274, G_304, D_290, E_298, B_242]: (r1_tmap_1(B_242, A_178, C_274, G_304) | ~r1_tmap_1(D_290, A_178, k2_tmap_1(B_242, A_178, C_274, D_290), G_304) | ~m1_connsp_2(E_298, B_242, G_304) | ~r1_tarski(E_298, u1_struct_0(D_290)) | ~m1_subset_1(G_304, u1_struct_0(D_290)) | ~m1_subset_1(G_304, u1_struct_0(B_242)) | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0(B_242))) | ~m1_pre_topc(D_290, B_242) | v2_struct_0(D_290) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_242), u1_struct_0(A_178)))) | ~v1_funct_2(C_274, u1_struct_0(B_242), u1_struct_0(A_178)) | ~v1_funct_1(C_274) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_284])).
% 8.55/3.03  tff(c_4762, plain, (![E_298]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(E_298, '#skF_5', '#skF_8') | ~r1_tarski(E_298, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4756, c_42])).
% 8.55/3.03  tff(c_4765, plain, (![E_298]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(E_298, '#skF_5', '#skF_8') | ~r1_tarski(E_298, u1_struct_0('#skF_4')) | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_169, c_128, c_68, c_66, c_64, c_62, c_58, c_99, c_4762])).
% 8.55/3.03  tff(c_4767, plain, (![E_878]: (~m1_connsp_2(E_878, '#skF_5', '#skF_8') | ~r1_tarski(E_878, u1_struct_0('#skF_4')) | ~m1_subset_1(E_878, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_88, c_72, c_76, c_248, c_4765])).
% 8.55/3.03  tff(c_4785, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8') | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3004, c_4767])).
% 8.55/3.03  tff(c_4843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2992, c_4785])).
% 8.55/3.03  tff(c_4844, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_97])).
% 8.55/3.03  tff(c_7089, plain, (![D_1090, F_1092, B_1091, A_1093, C_1089]: (r1_tmap_1(D_1090, A_1093, k2_tmap_1(B_1091, A_1093, C_1089, D_1090), F_1092) | ~r1_tmap_1(B_1091, A_1093, C_1089, F_1092) | ~m1_subset_1(F_1092, u1_struct_0(D_1090)) | ~m1_subset_1(F_1092, u1_struct_0(B_1091)) | ~m1_pre_topc(D_1090, B_1091) | v2_struct_0(D_1090) | ~m1_subset_1(C_1089, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1091), u1_struct_0(A_1093)))) | ~v1_funct_2(C_1089, u1_struct_0(B_1091), u1_struct_0(A_1093)) | ~v1_funct_1(C_1089) | ~l1_pre_topc(B_1091) | ~v2_pre_topc(B_1091) | v2_struct_0(B_1091) | ~l1_pre_topc(A_1093) | ~v2_pre_topc(A_1093) | v2_struct_0(A_1093))), inference(cnfTransformation, [status(thm)], [f_237])).
% 8.55/3.03  tff(c_7091, plain, (![D_1090, F_1092]: (r1_tmap_1(D_1090, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1090), F_1092) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1092) | ~m1_subset_1(F_1092, u1_struct_0(D_1090)) | ~m1_subset_1(F_1092, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1090, '#skF_5') | v2_struct_0(D_1090) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_7089])).
% 8.55/3.03  tff(c_7097, plain, (![D_1090, F_1092]: (r1_tmap_1(D_1090, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1090), F_1092) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1092) | ~m1_subset_1(F_1092, u1_struct_0(D_1090)) | ~m1_subset_1(F_1092, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1090, '#skF_5') | v2_struct_0(D_1090) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_169, c_128, c_68, c_66, c_7091])).
% 8.55/3.03  tff(c_7098, plain, (![D_1090, F_1092]: (r1_tmap_1(D_1090, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1090), F_1092) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1092) | ~m1_subset_1(F_1092, u1_struct_0(D_1090)) | ~m1_subset_1(F_1092, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1090, '#skF_5') | v2_struct_0(D_1090))), inference(negUnitSimplification, [status(thm)], [c_88, c_72, c_7097])).
% 8.55/3.03  tff(c_6757, plain, (![B_1075, A_1074, C_1076, D_1077, E_1073]: (k3_tmap_1(A_1074, B_1075, C_1076, D_1077, E_1073)=k2_partfun1(u1_struct_0(C_1076), u1_struct_0(B_1075), E_1073, u1_struct_0(D_1077)) | ~m1_pre_topc(D_1077, C_1076) | ~m1_subset_1(E_1073, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1076), u1_struct_0(B_1075)))) | ~v1_funct_2(E_1073, u1_struct_0(C_1076), u1_struct_0(B_1075)) | ~v1_funct_1(E_1073) | ~m1_pre_topc(D_1077, A_1074) | ~m1_pre_topc(C_1076, A_1074) | ~l1_pre_topc(B_1075) | ~v2_pre_topc(B_1075) | v2_struct_0(B_1075) | ~l1_pre_topc(A_1074) | ~v2_pre_topc(A_1074) | v2_struct_0(A_1074))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.55/3.03  tff(c_6759, plain, (![A_1074, D_1077]: (k3_tmap_1(A_1074, '#skF_2', '#skF_5', D_1077, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1077)) | ~m1_pre_topc(D_1077, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_1077, A_1074) | ~m1_pre_topc('#skF_5', A_1074) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1074) | ~v2_pre_topc(A_1074) | v2_struct_0(A_1074))), inference(resolution, [status(thm)], [c_64, c_6757])).
% 8.55/3.03  tff(c_6765, plain, (![A_1074, D_1077]: (k3_tmap_1(A_1074, '#skF_2', '#skF_5', D_1077, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1077)) | ~m1_pre_topc(D_1077, '#skF_5') | ~m1_pre_topc(D_1077, A_1074) | ~m1_pre_topc('#skF_5', A_1074) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1074) | ~v2_pre_topc(A_1074) | v2_struct_0(A_1074))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_68, c_66, c_6759])).
% 8.55/3.03  tff(c_9365, plain, (![A_1182, D_1183]: (k3_tmap_1(A_1182, '#skF_2', '#skF_5', D_1183, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1183)) | ~m1_pre_topc(D_1183, '#skF_5') | ~m1_pre_topc(D_1183, A_1182) | ~m1_pre_topc('#skF_5', A_1182) | ~l1_pre_topc(A_1182) | ~v2_pre_topc(A_1182) | v2_struct_0(A_1182))), inference(negUnitSimplification, [status(thm)], [c_88, c_6765])).
% 8.55/3.03  tff(c_9373, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_9365])).
% 8.55/3.03  tff(c_9385, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_70, c_62, c_9373])).
% 8.55/3.03  tff(c_9386, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_82, c_9385])).
% 8.55/3.03  tff(c_6494, plain, (![A_1060, B_1061, C_1062, D_1063]: (k2_partfun1(u1_struct_0(A_1060), u1_struct_0(B_1061), C_1062, u1_struct_0(D_1063))=k2_tmap_1(A_1060, B_1061, C_1062, D_1063) | ~m1_pre_topc(D_1063, A_1060) | ~m1_subset_1(C_1062, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1060), u1_struct_0(B_1061)))) | ~v1_funct_2(C_1062, u1_struct_0(A_1060), u1_struct_0(B_1061)) | ~v1_funct_1(C_1062) | ~l1_pre_topc(B_1061) | ~v2_pre_topc(B_1061) | v2_struct_0(B_1061) | ~l1_pre_topc(A_1060) | ~v2_pre_topc(A_1060) | v2_struct_0(A_1060))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.55/3.03  tff(c_6496, plain, (![D_1063]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1063))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1063) | ~m1_pre_topc(D_1063, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_6494])).
% 8.55/3.03  tff(c_6502, plain, (![D_1063]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1063))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1063) | ~m1_pre_topc(D_1063, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_128, c_86, c_84, c_68, c_66, c_6496])).
% 8.55/3.03  tff(c_6503, plain, (![D_1063]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1063))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1063) | ~m1_pre_topc(D_1063, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_88, c_6502])).
% 8.55/3.03  tff(c_9390, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9386, c_6503])).
% 8.55/3.03  tff(c_9397, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9390])).
% 8.55/3.03  tff(c_4845, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_97])).
% 8.55/3.03  tff(c_9402, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9397, c_4845])).
% 8.55/3.03  tff(c_9409, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_7098, c_9402])).
% 8.55/3.03  tff(c_9412, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_99, c_4844, c_9409])).
% 8.55/3.03  tff(c_9414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_9412])).
% 8.55/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.03  
% 8.55/3.03  Inference rules
% 8.55/3.03  ----------------------
% 8.55/3.03  #Ref     : 0
% 8.55/3.03  #Sup     : 1739
% 8.55/3.03  #Fact    : 0
% 8.55/3.03  #Define  : 0
% 8.55/3.03  #Split   : 29
% 8.55/3.03  #Chain   : 0
% 8.55/3.03  #Close   : 0
% 8.55/3.03  
% 8.55/3.03  Ordering : KBO
% 8.55/3.03  
% 8.55/3.03  Simplification rules
% 8.55/3.03  ----------------------
% 8.55/3.03  #Subsume      : 589
% 8.55/3.03  #Demod        : 1864
% 8.55/3.03  #Tautology    : 256
% 8.55/3.03  #SimpNegUnit  : 248
% 8.55/3.03  #BackRed      : 4
% 8.55/3.03  
% 8.55/3.03  #Partial instantiations: 0
% 8.55/3.03  #Strategies tried      : 1
% 8.55/3.03  
% 8.55/3.03  Timing (in seconds)
% 8.55/3.03  ----------------------
% 8.55/3.03  Preprocessing        : 0.45
% 8.55/3.03  Parsing              : 0.22
% 8.55/3.04  CNF conversion       : 0.06
% 8.55/3.04  Main loop            : 1.83
% 8.55/3.04  Inferencing          : 0.60
% 8.55/3.04  Reduction            : 0.65
% 8.55/3.04  Demodulation         : 0.46
% 8.55/3.04  BG Simplification    : 0.06
% 8.55/3.04  Subsumption          : 0.40
% 8.55/3.04  Abstraction          : 0.06
% 8.55/3.04  MUC search           : 0.00
% 8.55/3.04  Cooper               : 0.00
% 8.55/3.04  Total                : 2.33
% 8.55/3.04  Index Insertion      : 0.00
% 8.55/3.04  Index Deletion       : 0.00
% 8.55/3.04  Index Matching       : 0.00
% 8.55/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
