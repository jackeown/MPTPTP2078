%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:18 EST 2020

% Result     : Theorem 13.03s
% Output     : CNFRefutation 13.12s
% Verified   : 
% Statistics : Number of formulae       :  236 (2815 expanded)
%              Number of leaves         :   44 ( 960 expanded)
%              Depth                    :   22
%              Number of atoms          :  944 (16864 expanded)
%              Number of equality atoms :   94 (1021 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_263,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_164,axiom,(
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

tff(f_132,axiom,(
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

tff(f_49,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_194,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_182,plain,(
    ! [C_237,B_238,A_239] :
      ( v1_xboole_0(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(B_238,A_239)))
      | ~ v1_xboole_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_196,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_182])).

tff(c_202,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_66,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_50,plain,(
    '#skF_6' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_54,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_101,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_102,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_48,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_103,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_3411,plain,(
    ! [C_951,D_952,E_953,A_955,B_954,F_950] :
      ( F_950 = E_953
      | ~ r1_funct_2(A_955,B_954,C_951,D_952,E_953,F_950)
      | ~ m1_subset_1(F_950,k1_zfmisc_1(k2_zfmisc_1(C_951,D_952)))
      | ~ v1_funct_2(F_950,C_951,D_952)
      | ~ v1_funct_1(F_950)
      | ~ m1_subset_1(E_953,k1_zfmisc_1(k2_zfmisc_1(A_955,B_954)))
      | ~ v1_funct_2(E_953,A_955,B_954)
      | ~ v1_funct_1(E_953)
      | v1_xboole_0(D_952)
      | v1_xboole_0(B_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3415,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_103,c_3411])).

tff(c_3423,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_56,c_101,c_102,c_3415])).

tff(c_3424,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_3423])).

tff(c_1787,plain,(
    ! [E_588,F_585,C_586,A_590,D_587,B_589] :
      ( F_585 = E_588
      | ~ r1_funct_2(A_590,B_589,C_586,D_587,E_588,F_585)
      | ~ m1_subset_1(F_585,k1_zfmisc_1(k2_zfmisc_1(C_586,D_587)))
      | ~ v1_funct_2(F_585,C_586,D_587)
      | ~ v1_funct_1(F_585)
      | ~ m1_subset_1(E_588,k1_zfmisc_1(k2_zfmisc_1(A_590,B_589)))
      | ~ v1_funct_2(E_588,A_590,B_589)
      | ~ v1_funct_1(E_588)
      | v1_xboole_0(D_587)
      | v1_xboole_0(B_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1789,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_103,c_1787])).

tff(c_1792,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_56,c_101,c_102,c_1789])).

tff(c_1793,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_1792])).

tff(c_96,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_98,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96])).

tff(c_316,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_1795,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_316])).

tff(c_74,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_86,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_70,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_99,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_70])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_80,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1993,plain,(
    ! [C_648,E_649,B_647,A_646,D_650] :
      ( k3_tmap_1(A_646,B_647,C_648,D_650,E_649) = k2_partfun1(u1_struct_0(C_648),u1_struct_0(B_647),E_649,u1_struct_0(D_650))
      | ~ m1_pre_topc(D_650,C_648)
      | ~ m1_subset_1(E_649,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_648),u1_struct_0(B_647))))
      | ~ v1_funct_2(E_649,u1_struct_0(C_648),u1_struct_0(B_647))
      | ~ v1_funct_1(E_649)
      | ~ m1_pre_topc(D_650,A_646)
      | ~ m1_pre_topc(C_648,A_646)
      | ~ l1_pre_topc(B_647)
      | ~ v2_pre_topc(B_647)
      | v2_struct_0(B_647)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2002,plain,(
    ! [A_646,D_650] :
      ( k3_tmap_1(A_646,'#skF_4','#skF_3',D_650,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_650))
      | ~ m1_pre_topc(D_650,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_650,A_646)
      | ~ m1_pre_topc('#skF_3',A_646)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(resolution,[status(thm)],[c_102,c_1993])).

tff(c_2011,plain,(
    ! [A_646,D_650] :
      ( k3_tmap_1(A_646,'#skF_4','#skF_3',D_650,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_650))
      | ~ m1_pre_topc(D_650,'#skF_3')
      | ~ m1_pre_topc(D_650,A_646)
      | ~ m1_pre_topc('#skF_3',A_646)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_56,c_101,c_2002])).

tff(c_2013,plain,(
    ! [A_651,D_652] :
      ( k3_tmap_1(A_651,'#skF_4','#skF_3',D_652,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_652))
      | ~ m1_pre_topc(D_652,'#skF_3')
      | ~ m1_pre_topc(D_652,A_651)
      | ~ m1_pre_topc('#skF_3',A_651)
      | ~ l1_pre_topc(A_651)
      | ~ v2_pre_topc(A_651)
      | v2_struct_0(A_651) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2011])).

tff(c_2017,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2013])).

tff(c_2025,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_74,c_2017])).

tff(c_2026,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2025])).

tff(c_1928,plain,(
    ! [A_627,B_628,C_629,D_630] :
      ( k2_partfun1(u1_struct_0(A_627),u1_struct_0(B_628),C_629,u1_struct_0(D_630)) = k2_tmap_1(A_627,B_628,C_629,D_630)
      | ~ m1_pre_topc(D_630,A_627)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_627),u1_struct_0(B_628))))
      | ~ v1_funct_2(C_629,u1_struct_0(A_627),u1_struct_0(B_628))
      | ~ v1_funct_1(C_629)
      | ~ l1_pre_topc(B_628)
      | ~ v2_pre_topc(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1935,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_630)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_630)
      | ~ m1_pre_topc(D_630,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_102,c_1928])).

tff(c_1943,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_630)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_630)
      | ~ m1_pre_topc(D_630,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_56,c_101,c_1935])).

tff(c_1944,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_630)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_630)
      | ~ m1_pre_topc(D_630,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_1943])).

tff(c_2034,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_1944])).

tff(c_2041,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2034])).

tff(c_90,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_100,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_90])).

tff(c_376,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_100])).

tff(c_2046,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2041,c_376])).

tff(c_2049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1795,c_2046])).

tff(c_2051,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3425,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_2051])).

tff(c_3638,plain,(
    ! [A_1013,E_1016,B_1014,D_1017,C_1015] :
      ( k3_tmap_1(A_1013,B_1014,C_1015,D_1017,E_1016) = k2_partfun1(u1_struct_0(C_1015),u1_struct_0(B_1014),E_1016,u1_struct_0(D_1017))
      | ~ m1_pre_topc(D_1017,C_1015)
      | ~ m1_subset_1(E_1016,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1015),u1_struct_0(B_1014))))
      | ~ v1_funct_2(E_1016,u1_struct_0(C_1015),u1_struct_0(B_1014))
      | ~ v1_funct_1(E_1016)
      | ~ m1_pre_topc(D_1017,A_1013)
      | ~ m1_pre_topc(C_1015,A_1013)
      | ~ l1_pre_topc(B_1014)
      | ~ v2_pre_topc(B_1014)
      | v2_struct_0(B_1014)
      | ~ l1_pre_topc(A_1013)
      | ~ v2_pre_topc(A_1013)
      | v2_struct_0(A_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3647,plain,(
    ! [A_1013,D_1017] :
      ( k3_tmap_1(A_1013,'#skF_4','#skF_3',D_1017,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_1017))
      | ~ m1_pre_topc(D_1017,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_1017,A_1013)
      | ~ m1_pre_topc('#skF_3',A_1013)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1013)
      | ~ v2_pre_topc(A_1013)
      | v2_struct_0(A_1013) ) ),
    inference(resolution,[status(thm)],[c_102,c_3638])).

tff(c_3656,plain,(
    ! [A_1013,D_1017] :
      ( k3_tmap_1(A_1013,'#skF_4','#skF_3',D_1017,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_1017))
      | ~ m1_pre_topc(D_1017,'#skF_3')
      | ~ m1_pre_topc(D_1017,A_1013)
      | ~ m1_pre_topc('#skF_3',A_1013)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1013)
      | ~ v2_pre_topc(A_1013)
      | v2_struct_0(A_1013) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_56,c_101,c_3647])).

tff(c_3680,plain,(
    ! [A_1020,D_1021] :
      ( k3_tmap_1(A_1020,'#skF_4','#skF_3',D_1021,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_1021))
      | ~ m1_pre_topc(D_1021,'#skF_3')
      | ~ m1_pre_topc(D_1021,A_1020)
      | ~ m1_pre_topc('#skF_3',A_1020)
      | ~ l1_pre_topc(A_1020)
      | ~ v2_pre_topc(A_1020)
      | v2_struct_0(A_1020) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_3656])).

tff(c_3684,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3680])).

tff(c_3692,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_74,c_3684])).

tff(c_3693,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3692])).

tff(c_3557,plain,(
    ! [A_991,B_992,C_993,D_994] :
      ( k2_partfun1(u1_struct_0(A_991),u1_struct_0(B_992),C_993,u1_struct_0(D_994)) = k2_tmap_1(A_991,B_992,C_993,D_994)
      | ~ m1_pre_topc(D_994,A_991)
      | ~ m1_subset_1(C_993,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_991),u1_struct_0(B_992))))
      | ~ v1_funct_2(C_993,u1_struct_0(A_991),u1_struct_0(B_992))
      | ~ v1_funct_1(C_993)
      | ~ l1_pre_topc(B_992)
      | ~ v2_pre_topc(B_992)
      | v2_struct_0(B_992)
      | ~ l1_pre_topc(A_991)
      | ~ v2_pre_topc(A_991)
      | v2_struct_0(A_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3564,plain,(
    ! [D_994] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_994)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_994)
      | ~ m1_pre_topc(D_994,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_102,c_3557])).

tff(c_3572,plain,(
    ! [D_994] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_994)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_994)
      | ~ m1_pre_topc(D_994,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_56,c_101,c_3564])).

tff(c_3573,plain,(
    ! [D_994] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_994)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_994)
      | ~ m1_pre_topc(D_994,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_3572])).

tff(c_3701,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3693,c_3573])).

tff(c_3708,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3701])).

tff(c_2050,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3714,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_2050])).

tff(c_3716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3425,c_3714])).

tff(c_3717,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_20,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_tarski(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tarski(A_14),k1_zfmisc_1(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_189,plain,(
    ! [A_14,A_239,B_238] :
      ( v1_xboole_0(k1_tarski(A_14))
      | ~ v1_xboole_0(A_239)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_238,A_239)) ) ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_3800,plain,(
    ! [A_1029,A_1030,B_1031] :
      ( ~ v1_xboole_0(A_1029)
      | ~ r2_hidden(A_1030,k2_zfmisc_1(B_1031,A_1029)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_189])).

tff(c_3811,plain,(
    ! [A_1032,B_1033] :
      ( ~ v1_xboole_0(A_1032)
      | v1_xboole_0(k2_zfmisc_1(B_1033,A_1032)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3800])).

tff(c_3718,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_127,plain,(
    ! [A_219,B_220] :
      ( r2_hidden('#skF_2'(A_219,B_220),A_219)
      | r1_tarski(A_219,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_219,B_220] :
      ( ~ v1_xboole_0(A_219)
      | r1_tarski(A_219,B_220) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_140,plain,(
    ! [B_225,A_226] :
      ( B_225 = A_226
      | ~ r1_tarski(B_225,A_226)
      | ~ r1_tarski(A_226,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [B_227,A_228] :
      ( B_227 = A_228
      | ~ r1_tarski(B_227,A_228)
      | ~ v1_xboole_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_131,c_140])).

tff(c_157,plain,(
    ! [B_220,A_219] :
      ( B_220 = A_219
      | ~ v1_xboole_0(B_220)
      | ~ v1_xboole_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_131,c_150])).

tff(c_3732,plain,(
    ! [A_1025] :
      ( A_1025 = '#skF_8'
      | ~ v1_xboole_0(A_1025) ) ),
    inference(resolution,[status(thm)],[c_3717,c_157])).

tff(c_3739,plain,(
    u1_struct_0('#skF_4') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3718,c_3732])).

tff(c_161,plain,(
    ! [C_231,B_232,A_233] :
      ( ~ v1_xboole_0(C_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(C_231))
      | ~ r2_hidden(A_233,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,(
    ! [A_233] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_233,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_102,c_161])).

tff(c_181,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_3799,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3739,c_181])).

tff(c_3814,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_3811,c_3799])).

tff(c_3823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3717,c_3814])).

tff(c_3826,plain,(
    ! [A_1034] : ~ r2_hidden(A_1034,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_3836,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_3826])).

tff(c_3825,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3861,plain,(
    ! [B_1038] : r1_tarski('#skF_9',B_1038) ),
    inference(resolution,[status(thm)],[c_10,c_3826])).

tff(c_145,plain,(
    ! [B_220,A_219] :
      ( B_220 = A_219
      | ~ r1_tarski(B_220,A_219)
      | ~ v1_xboole_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_131,c_140])).

tff(c_3867,plain,(
    ! [B_1038] :
      ( B_1038 = '#skF_9'
      | ~ v1_xboole_0(B_1038) ) ),
    inference(resolution,[status(thm)],[c_3861,c_145])).

tff(c_3899,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3825,c_3867])).

tff(c_3903,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_64])).

tff(c_24,plain,(
    ! [C_18,B_17,A_16] :
      ( ~ v1_xboole_0(C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(C_18))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3925,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(A_16,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3903,c_24])).

tff(c_3929,plain,(
    ! [A_1044] : ~ r2_hidden(A_1044,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3836,c_3925])).

tff(c_3939,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_3929])).

tff(c_3947,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3939,c_3867])).

tff(c_4080,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3947,c_98])).

tff(c_4081,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4080])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_60,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_6656,plain,(
    ! [A_1264,C_1265,D_1263,E_1267,B_1266] :
      ( m1_subset_1(k3_tmap_1(A_1264,B_1266,C_1265,D_1263,E_1267),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1263),u1_struct_0(B_1266))))
      | ~ m1_subset_1(E_1267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265),u1_struct_0(B_1266))))
      | ~ v1_funct_2(E_1267,u1_struct_0(C_1265),u1_struct_0(B_1266))
      | ~ v1_funct_1(E_1267)
      | ~ m1_pre_topc(D_1263,A_1264)
      | ~ m1_pre_topc(C_1265,A_1264)
      | ~ l1_pre_topc(B_1266)
      | ~ v2_pre_topc(B_1266)
      | v2_struct_0(B_1266)
      | ~ l1_pre_topc(A_1264)
      | ~ v2_pre_topc(A_1264)
      | v2_struct_0(A_1264) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_6674,plain,(
    ! [A_1264,C_1265,E_1267] :
      ( m1_subset_1(k3_tmap_1(A_1264,'#skF_4',C_1265,'#skF_3',E_1267),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1267,u1_struct_0(C_1265),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1267)
      | ~ m1_pre_topc('#skF_3',A_1264)
      | ~ m1_pre_topc(C_1265,A_1264)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1264)
      | ~ v2_pre_topc(A_1264)
      | v2_struct_0(A_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3899,c_6656])).

tff(c_6683,plain,(
    ! [A_1264,C_1265,E_1267] :
      ( m1_subset_1(k3_tmap_1(A_1264,'#skF_4',C_1265,'#skF_3',E_1267),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1267,u1_struct_0(C_1265),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1267)
      | ~ m1_pre_topc('#skF_3',A_1264)
      | ~ m1_pre_topc(C_1265,A_1264)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1264)
      | ~ v2_pre_topc(A_1264)
      | v2_struct_0(A_1264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_6674])).

tff(c_8770,plain,(
    ! [A_1353,C_1354,E_1355] :
      ( m1_subset_1(k3_tmap_1(A_1353,'#skF_4',C_1354,'#skF_3',E_1355),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1354),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1355,u1_struct_0(C_1354),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1355)
      | ~ m1_pre_topc('#skF_3',A_1353)
      | ~ m1_pre_topc(C_1354,A_1353)
      | ~ l1_pre_topc(A_1353)
      | ~ v2_pre_topc(A_1353)
      | v2_struct_0(A_1353) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6683])).

tff(c_8777,plain,(
    ! [A_1353] :
      ( m1_subset_1(k3_tmap_1(A_1353,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc('#skF_3',A_1353)
      | ~ m1_pre_topc('#skF_5',A_1353)
      | ~ l1_pre_topc(A_1353)
      | ~ v2_pre_topc(A_1353)
      | v2_struct_0(A_1353) ) ),
    inference(resolution,[status(thm)],[c_58,c_8770])).

tff(c_17299,plain,(
    ! [A_1626] :
      ( m1_subset_1(k3_tmap_1(A_1626,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ m1_pre_topc('#skF_3',A_1626)
      | ~ m1_pre_topc('#skF_5',A_1626)
      | ~ l1_pre_topc(A_1626)
      | ~ v2_pre_topc(A_1626)
      | v2_struct_0(A_1626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8777])).

tff(c_3840,plain,(
    ! [C_1035,B_1036,A_1037] :
      ( v1_xboole_0(C_1035)
      | ~ m1_subset_1(C_1035,k1_zfmisc_1(k2_zfmisc_1(B_1036,A_1037)))
      | ~ v1_xboole_0(A_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3847,plain,(
    ! [A_14,A_1037,B_1036] :
      ( v1_xboole_0(k1_tarski(A_14))
      | ~ v1_xboole_0(A_1037)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_1036,A_1037)) ) ),
    inference(resolution,[status(thm)],[c_22,c_3840])).

tff(c_3965,plain,(
    ! [A_1045,A_1046,B_1047] :
      ( ~ v1_xboole_0(A_1045)
      | ~ r2_hidden(A_1046,k2_zfmisc_1(B_1047,A_1045)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_3847])).

tff(c_3991,plain,(
    ! [A_1051,B_1052] :
      ( ~ v1_xboole_0(A_1051)
      | v1_xboole_0(k2_zfmisc_1(B_1052,A_1051)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3965])).

tff(c_4003,plain,(
    ! [B_1053,A_1054] :
      ( k2_zfmisc_1(B_1053,A_1054) = '#skF_9'
      | ~ v1_xboole_0(A_1054) ) ),
    inference(resolution,[status(thm)],[c_3991,c_3867])).

tff(c_4010,plain,(
    ! [B_1055] : k2_zfmisc_1(B_1055,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3836,c_4003])).

tff(c_26,plain,(
    ! [C_22,B_20,A_19] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4023,plain,(
    ! [C_22] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1('#skF_9'))
      | ~ v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4010,c_26])).

tff(c_4032,plain,(
    ! [C_22] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3836,c_4023])).

tff(c_17312,plain,(
    ! [A_1627] :
      ( v1_xboole_0(k3_tmap_1(A_1627,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ m1_pre_topc('#skF_3',A_1627)
      | ~ m1_pre_topc('#skF_5',A_1627)
      | ~ l1_pre_topc(A_1627)
      | ~ v2_pre_topc(A_1627)
      | v2_struct_0(A_1627) ) ),
    inference(resolution,[status(thm)],[c_17299,c_4032])).

tff(c_17359,plain,(
    ! [A_1628] :
      ( k3_tmap_1(A_1628,'#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
      | ~ m1_pre_topc('#skF_3',A_1628)
      | ~ m1_pre_topc('#skF_5',A_1628)
      | ~ l1_pre_topc(A_1628)
      | ~ v2_pre_topc(A_1628)
      | v2_struct_0(A_1628) ) ),
    inference(resolution,[status(thm)],[c_17312,c_3867])).

tff(c_17365,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_17359])).

tff(c_17369,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_17365])).

tff(c_17370,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_17369])).

tff(c_3902,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_102])).

tff(c_36,plain,(
    ! [A_33,B_41,C_45,D_47] :
      ( k2_partfun1(u1_struct_0(A_33),u1_struct_0(B_41),C_45,u1_struct_0(D_47)) = k2_tmap_1(A_33,B_41,C_45,D_47)
      | ~ m1_pre_topc(D_47,A_33)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33),u1_struct_0(B_41))))
      | ~ v1_funct_2(C_45,u1_struct_0(A_33),u1_struct_0(B_41))
      | ~ v1_funct_1(C_45)
      | ~ l1_pre_topc(B_41)
      | ~ v2_pre_topc(B_41)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14237,plain,(
    ! [E_1564,C_1561,D_1560,B_1562,D_1559,A_1563] :
      ( k2_partfun1(u1_struct_0(D_1559),u1_struct_0(B_1562),k3_tmap_1(A_1563,B_1562,C_1561,D_1559,E_1564),u1_struct_0(D_1560)) = k2_tmap_1(D_1559,B_1562,k3_tmap_1(A_1563,B_1562,C_1561,D_1559,E_1564),D_1560)
      | ~ m1_pre_topc(D_1560,D_1559)
      | ~ v1_funct_2(k3_tmap_1(A_1563,B_1562,C_1561,D_1559,E_1564),u1_struct_0(D_1559),u1_struct_0(B_1562))
      | ~ v1_funct_1(k3_tmap_1(A_1563,B_1562,C_1561,D_1559,E_1564))
      | ~ l1_pre_topc(D_1559)
      | ~ v2_pre_topc(D_1559)
      | v2_struct_0(D_1559)
      | ~ m1_subset_1(E_1564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1561),u1_struct_0(B_1562))))
      | ~ v1_funct_2(E_1564,u1_struct_0(C_1561),u1_struct_0(B_1562))
      | ~ v1_funct_1(E_1564)
      | ~ m1_pre_topc(D_1559,A_1563)
      | ~ m1_pre_topc(C_1561,A_1563)
      | ~ l1_pre_topc(B_1562)
      | ~ v2_pre_topc(B_1562)
      | v2_struct_0(B_1562)
      | ~ l1_pre_topc(A_1563)
      | ~ v2_pre_topc(A_1563)
      | v2_struct_0(A_1563) ) ),
    inference(resolution,[status(thm)],[c_6656,c_36])).

tff(c_14243,plain,(
    ! [D_1559,A_1563,D_1560] :
      ( k2_partfun1(u1_struct_0(D_1559),u1_struct_0('#skF_4'),k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),u1_struct_0(D_1560)) = k2_tmap_1(D_1559,'#skF_4',k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),D_1560)
      | ~ m1_pre_topc(D_1560,D_1559)
      | ~ v1_funct_2(k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),u1_struct_0(D_1559),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'))
      | ~ l1_pre_topc(D_1559)
      | ~ v2_pre_topc(D_1559)
      | v2_struct_0(D_1559)
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_1559,A_1563)
      | ~ m1_pre_topc('#skF_5',A_1563)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1563)
      | ~ v2_pre_topc(A_1563)
      | v2_struct_0(A_1563) ) ),
    inference(resolution,[status(thm)],[c_58,c_14237])).

tff(c_14253,plain,(
    ! [D_1559,A_1563,D_1560] :
      ( k2_partfun1(u1_struct_0(D_1559),u1_struct_0('#skF_4'),k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),u1_struct_0(D_1560)) = k2_tmap_1(D_1559,'#skF_4',k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),D_1560)
      | ~ m1_pre_topc(D_1560,D_1559)
      | ~ v1_funct_2(k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'),u1_struct_0(D_1559),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1563,'#skF_4','#skF_5',D_1559,'#skF_8'))
      | ~ l1_pre_topc(D_1559)
      | ~ v2_pre_topc(D_1559)
      | v2_struct_0(D_1559)
      | ~ m1_pre_topc(D_1559,A_1563)
      | ~ m1_pre_topc('#skF_5',A_1563)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1563)
      | ~ v2_pre_topc(A_1563)
      | v2_struct_0(A_1563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_60,c_14243])).

tff(c_14256,plain,(
    ! [D_1565,A_1566,D_1567] :
      ( k2_partfun1(u1_struct_0(D_1565),u1_struct_0('#skF_4'),k3_tmap_1(A_1566,'#skF_4','#skF_5',D_1565,'#skF_8'),u1_struct_0(D_1567)) = k2_tmap_1(D_1565,'#skF_4',k3_tmap_1(A_1566,'#skF_4','#skF_5',D_1565,'#skF_8'),D_1567)
      | ~ m1_pre_topc(D_1567,D_1565)
      | ~ v1_funct_2(k3_tmap_1(A_1566,'#skF_4','#skF_5',D_1565,'#skF_8'),u1_struct_0(D_1565),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1566,'#skF_4','#skF_5',D_1565,'#skF_8'))
      | ~ l1_pre_topc(D_1565)
      | ~ v2_pre_topc(D_1565)
      | v2_struct_0(D_1565)
      | ~ m1_pre_topc(D_1565,A_1566)
      | ~ m1_pre_topc('#skF_5',A_1566)
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_14253])).

tff(c_7103,plain,(
    ! [B_1283,E_1285,A_1282,C_1284,D_1286] :
      ( k3_tmap_1(A_1282,B_1283,C_1284,D_1286,E_1285) = k2_partfun1(u1_struct_0(C_1284),u1_struct_0(B_1283),E_1285,u1_struct_0(D_1286))
      | ~ m1_pre_topc(D_1286,C_1284)
      | ~ m1_subset_1(E_1285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1284),u1_struct_0(B_1283))))
      | ~ v1_funct_2(E_1285,u1_struct_0(C_1284),u1_struct_0(B_1283))
      | ~ v1_funct_1(E_1285)
      | ~ m1_pre_topc(D_1286,A_1282)
      | ~ m1_pre_topc(C_1284,A_1282)
      | ~ l1_pre_topc(B_1283)
      | ~ v2_pre_topc(B_1283)
      | v2_struct_0(B_1283)
      | ~ l1_pre_topc(A_1282)
      | ~ v2_pre_topc(A_1282)
      | v2_struct_0(A_1282) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_7107,plain,(
    ! [A_1282,D_1286,E_1285] :
      ( k3_tmap_1(A_1282,'#skF_4','#skF_3',D_1286,E_1285) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1285,u1_struct_0(D_1286))
      | ~ m1_pre_topc(D_1286,'#skF_3')
      | ~ m1_subset_1(E_1285,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1285,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1285)
      | ~ m1_pre_topc(D_1286,A_1282)
      | ~ m1_pre_topc('#skF_3',A_1282)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1282)
      | ~ v2_pre_topc(A_1282)
      | v2_struct_0(A_1282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3899,c_7103])).

tff(c_7115,plain,(
    ! [A_1282,D_1286,E_1285] :
      ( k3_tmap_1(A_1282,'#skF_4','#skF_3',D_1286,E_1285) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1285,u1_struct_0(D_1286))
      | ~ m1_pre_topc(D_1286,'#skF_3')
      | ~ m1_subset_1(E_1285,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1285,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1285)
      | ~ m1_pre_topc(D_1286,A_1282)
      | ~ m1_pre_topc('#skF_3',A_1282)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1282)
      | ~ v2_pre_topc(A_1282)
      | v2_struct_0(A_1282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_7107])).

tff(c_9783,plain,(
    ! [A_1375,D_1376,E_1377] :
      ( k3_tmap_1(A_1375,'#skF_4','#skF_3',D_1376,E_1377) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1377,u1_struct_0(D_1376))
      | ~ m1_pre_topc(D_1376,'#skF_3')
      | ~ m1_subset_1(E_1377,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1377,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1377)
      | ~ m1_pre_topc(D_1376,A_1375)
      | ~ m1_pre_topc('#skF_3',A_1375)
      | ~ l1_pre_topc(A_1375)
      | ~ v2_pre_topc(A_1375)
      | v2_struct_0(A_1375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7115])).

tff(c_9787,plain,(
    ! [E_1377] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1377,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1377)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(E_1377,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1377,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1377)
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_9783])).

tff(c_9795,plain,(
    ! [E_1377] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1377,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1377)
      | ~ m1_subset_1(E_1377,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1377,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1377)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_74,c_9787])).

tff(c_9796,plain,(
    ! [E_1377] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1377,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1377)
      | ~ m1_subset_1(E_1377,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1377,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_9795])).

tff(c_14267,plain,(
    ! [A_1566] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ v1_funct_2(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1566)
      | ~ m1_pre_topc('#skF_5',A_1566)
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14256,c_9796])).

tff(c_14292,plain,(
    ! [A_1566] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1566)
      | ~ m1_pre_topc('#skF_5',A_1566)
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_14267])).

tff(c_14293,plain,(
    ! [A_1566] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_1566,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ m1_pre_topc('#skF_3',A_1566)
      | ~ m1_pre_topc('#skF_5',A_1566)
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_14292])).

tff(c_17385,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17370,c_14293])).

tff(c_17434,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_99,c_56,c_17370,c_101,c_3902,c_17370,c_17370,c_17370,c_17385])).

tff(c_17435,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_17434])).

tff(c_4229,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3947,c_100])).

tff(c_4230,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4229])).

tff(c_17486,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17435,c_4230])).

tff(c_17489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4081,c_17486])).

tff(c_17490,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4229])).

tff(c_17615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17490,c_4081])).

tff(c_17616,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4080])).

tff(c_17706,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3947,c_100])).

tff(c_17707,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_17706])).

tff(c_17931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17616,c_17707])).

tff(c_17932,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_17706])).

tff(c_20235,plain,(
    ! [A_1883,E_1886,B_1885,D_1882,C_1884] :
      ( m1_subset_1(k3_tmap_1(A_1883,B_1885,C_1884,D_1882,E_1886),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1882),u1_struct_0(B_1885))))
      | ~ m1_subset_1(E_1886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884),u1_struct_0(B_1885))))
      | ~ v1_funct_2(E_1886,u1_struct_0(C_1884),u1_struct_0(B_1885))
      | ~ v1_funct_1(E_1886)
      | ~ m1_pre_topc(D_1882,A_1883)
      | ~ m1_pre_topc(C_1884,A_1883)
      | ~ l1_pre_topc(B_1885)
      | ~ v2_pre_topc(B_1885)
      | v2_struct_0(B_1885)
      | ~ l1_pre_topc(A_1883)
      | ~ v2_pre_topc(A_1883)
      | v2_struct_0(A_1883) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_20253,plain,(
    ! [A_1883,C_1884,E_1886] :
      ( m1_subset_1(k3_tmap_1(A_1883,'#skF_4',C_1884,'#skF_3',E_1886),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1886,u1_struct_0(C_1884),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1886)
      | ~ m1_pre_topc('#skF_3',A_1883)
      | ~ m1_pre_topc(C_1884,A_1883)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1883)
      | ~ v2_pre_topc(A_1883)
      | v2_struct_0(A_1883) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3899,c_20235])).

tff(c_20262,plain,(
    ! [A_1883,C_1884,E_1886] :
      ( m1_subset_1(k3_tmap_1(A_1883,'#skF_4',C_1884,'#skF_3',E_1886),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1886,u1_struct_0(C_1884),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1886)
      | ~ m1_pre_topc('#skF_3',A_1883)
      | ~ m1_pre_topc(C_1884,A_1883)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1883)
      | ~ v2_pre_topc(A_1883)
      | v2_struct_0(A_1883) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_20253])).

tff(c_21774,plain,(
    ! [A_1977,C_1978,E_1979] :
      ( m1_subset_1(k3_tmap_1(A_1977,'#skF_4',C_1978,'#skF_3',E_1979),k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(E_1979,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1978),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_1979,u1_struct_0(C_1978),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1979)
      | ~ m1_pre_topc('#skF_3',A_1977)
      | ~ m1_pre_topc(C_1978,A_1977)
      | ~ l1_pre_topc(A_1977)
      | ~ v2_pre_topc(A_1977)
      | v2_struct_0(A_1977) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_20262])).

tff(c_21781,plain,(
    ! [A_1977] :
      ( m1_subset_1(k3_tmap_1(A_1977,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc('#skF_3',A_1977)
      | ~ m1_pre_topc('#skF_5',A_1977)
      | ~ l1_pre_topc(A_1977)
      | ~ v2_pre_topc(A_1977)
      | v2_struct_0(A_1977) ) ),
    inference(resolution,[status(thm)],[c_58,c_21774])).

tff(c_31028,plain,(
    ! [A_2261] :
      ( m1_subset_1(k3_tmap_1(A_2261,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ m1_pre_topc('#skF_3',A_2261)
      | ~ m1_pre_topc('#skF_5',A_2261)
      | ~ l1_pre_topc(A_2261)
      | ~ v2_pre_topc(A_2261)
      | v2_struct_0(A_2261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_21781])).

tff(c_31151,plain,(
    ! [A_2266] :
      ( v1_xboole_0(k3_tmap_1(A_2266,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ m1_pre_topc('#skF_3',A_2266)
      | ~ m1_pre_topc('#skF_5',A_2266)
      | ~ l1_pre_topc(A_2266)
      | ~ v2_pre_topc(A_2266)
      | v2_struct_0(A_2266) ) ),
    inference(resolution,[status(thm)],[c_31028,c_4032])).

tff(c_31198,plain,(
    ! [A_2267] :
      ( k3_tmap_1(A_2267,'#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
      | ~ m1_pre_topc('#skF_3',A_2267)
      | ~ m1_pre_topc('#skF_5',A_2267)
      | ~ l1_pre_topc(A_2267)
      | ~ v2_pre_topc(A_2267)
      | v2_struct_0(A_2267) ) ),
    inference(resolution,[status(thm)],[c_31151,c_3867])).

tff(c_31204,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_31198])).

tff(c_31208,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_31204])).

tff(c_31209,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_31208])).

tff(c_20861,plain,(
    ! [E_1917,D_1918,C_1916,B_1915,A_1914] :
      ( k3_tmap_1(A_1914,B_1915,C_1916,D_1918,E_1917) = k2_partfun1(u1_struct_0(C_1916),u1_struct_0(B_1915),E_1917,u1_struct_0(D_1918))
      | ~ m1_pre_topc(D_1918,C_1916)
      | ~ m1_subset_1(E_1917,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1916),u1_struct_0(B_1915))))
      | ~ v1_funct_2(E_1917,u1_struct_0(C_1916),u1_struct_0(B_1915))
      | ~ v1_funct_1(E_1917)
      | ~ m1_pre_topc(D_1918,A_1914)
      | ~ m1_pre_topc(C_1916,A_1914)
      | ~ l1_pre_topc(B_1915)
      | ~ v2_pre_topc(B_1915)
      | v2_struct_0(B_1915)
      | ~ l1_pre_topc(A_1914)
      | ~ v2_pre_topc(A_1914)
      | v2_struct_0(A_1914) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_20865,plain,(
    ! [A_1914,D_1918,E_1917] :
      ( k3_tmap_1(A_1914,'#skF_4','#skF_3',D_1918,E_1917) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1917,u1_struct_0(D_1918))
      | ~ m1_pre_topc(D_1918,'#skF_3')
      | ~ m1_subset_1(E_1917,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1917,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1917)
      | ~ m1_pre_topc(D_1918,A_1914)
      | ~ m1_pre_topc('#skF_3',A_1914)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1914)
      | ~ v2_pre_topc(A_1914)
      | v2_struct_0(A_1914) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3899,c_20861])).

tff(c_20873,plain,(
    ! [A_1914,D_1918,E_1917] :
      ( k3_tmap_1(A_1914,'#skF_4','#skF_3',D_1918,E_1917) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1917,u1_struct_0(D_1918))
      | ~ m1_pre_topc(D_1918,'#skF_3')
      | ~ m1_subset_1(E_1917,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1917,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1917)
      | ~ m1_pre_topc(D_1918,A_1914)
      | ~ m1_pre_topc('#skF_3',A_1914)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1914)
      | ~ v2_pre_topc(A_1914)
      | v2_struct_0(A_1914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_20865])).

tff(c_21812,plain,(
    ! [A_1985,D_1986,E_1987] :
      ( k3_tmap_1(A_1985,'#skF_4','#skF_3',D_1986,E_1987) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1987,u1_struct_0(D_1986))
      | ~ m1_pre_topc(D_1986,'#skF_3')
      | ~ m1_subset_1(E_1987,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1987,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1987)
      | ~ m1_pre_topc(D_1986,A_1985)
      | ~ m1_pre_topc('#skF_3',A_1985)
      | ~ l1_pre_topc(A_1985)
      | ~ v2_pre_topc(A_1985)
      | v2_struct_0(A_1985) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_20873])).

tff(c_21816,plain,(
    ! [E_1987] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1987,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1987)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(E_1987,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1987,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1987)
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_21812])).

tff(c_21824,plain,(
    ! [E_1987] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1987,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1987)
      | ~ m1_subset_1(E_1987,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1987,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1987)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_99,c_74,c_21816])).

tff(c_21825,plain,(
    ! [E_1987] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),E_1987,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',E_1987)
      | ~ m1_subset_1(E_1987,k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(E_1987,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_1987) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_21824])).

tff(c_26482,plain,(
    ! [D_2166,B_2169,A_2167,D_2170,E_2171,C_2168] :
      ( k2_partfun1(u1_struct_0(D_2170),u1_struct_0(B_2169),k3_tmap_1(A_2167,B_2169,C_2168,D_2170,E_2171),u1_struct_0(D_2166)) = k2_tmap_1(D_2170,B_2169,k3_tmap_1(A_2167,B_2169,C_2168,D_2170,E_2171),D_2166)
      | ~ m1_pre_topc(D_2166,D_2170)
      | ~ v1_funct_2(k3_tmap_1(A_2167,B_2169,C_2168,D_2170,E_2171),u1_struct_0(D_2170),u1_struct_0(B_2169))
      | ~ v1_funct_1(k3_tmap_1(A_2167,B_2169,C_2168,D_2170,E_2171))
      | ~ l1_pre_topc(D_2170)
      | ~ v2_pre_topc(D_2170)
      | v2_struct_0(D_2170)
      | ~ m1_subset_1(E_2171,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_2168),u1_struct_0(B_2169))))
      | ~ v1_funct_2(E_2171,u1_struct_0(C_2168),u1_struct_0(B_2169))
      | ~ v1_funct_1(E_2171)
      | ~ m1_pre_topc(D_2170,A_2167)
      | ~ m1_pre_topc(C_2168,A_2167)
      | ~ l1_pre_topc(B_2169)
      | ~ v2_pre_topc(B_2169)
      | v2_struct_0(B_2169)
      | ~ l1_pre_topc(A_2167)
      | ~ v2_pre_topc(A_2167)
      | v2_struct_0(A_2167) ) ),
    inference(resolution,[status(thm)],[c_20235,c_36])).

tff(c_26488,plain,(
    ! [D_2170,A_2167,D_2166] :
      ( k2_partfun1(u1_struct_0(D_2170),u1_struct_0('#skF_4'),k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),u1_struct_0(D_2166)) = k2_tmap_1(D_2170,'#skF_4',k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),D_2166)
      | ~ m1_pre_topc(D_2166,D_2170)
      | ~ v1_funct_2(k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),u1_struct_0(D_2170),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'))
      | ~ l1_pre_topc(D_2170)
      | ~ v2_pre_topc(D_2170)
      | v2_struct_0(D_2170)
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_2170,A_2167)
      | ~ m1_pre_topc('#skF_5',A_2167)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_2167)
      | ~ v2_pre_topc(A_2167)
      | v2_struct_0(A_2167) ) ),
    inference(resolution,[status(thm)],[c_58,c_26482])).

tff(c_26498,plain,(
    ! [D_2170,A_2167,D_2166] :
      ( k2_partfun1(u1_struct_0(D_2170),u1_struct_0('#skF_4'),k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),u1_struct_0(D_2166)) = k2_tmap_1(D_2170,'#skF_4',k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),D_2166)
      | ~ m1_pre_topc(D_2166,D_2170)
      | ~ v1_funct_2(k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'),u1_struct_0(D_2170),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2167,'#skF_4','#skF_5',D_2170,'#skF_8'))
      | ~ l1_pre_topc(D_2170)
      | ~ v2_pre_topc(D_2170)
      | v2_struct_0(D_2170)
      | ~ m1_pre_topc(D_2170,A_2167)
      | ~ m1_pre_topc('#skF_5',A_2167)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_2167)
      | ~ v2_pre_topc(A_2167)
      | v2_struct_0(A_2167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_60,c_26488])).

tff(c_26501,plain,(
    ! [D_2172,A_2173,D_2174] :
      ( k2_partfun1(u1_struct_0(D_2172),u1_struct_0('#skF_4'),k3_tmap_1(A_2173,'#skF_4','#skF_5',D_2172,'#skF_8'),u1_struct_0(D_2174)) = k2_tmap_1(D_2172,'#skF_4',k3_tmap_1(A_2173,'#skF_4','#skF_5',D_2172,'#skF_8'),D_2174)
      | ~ m1_pre_topc(D_2174,D_2172)
      | ~ v1_funct_2(k3_tmap_1(A_2173,'#skF_4','#skF_5',D_2172,'#skF_8'),u1_struct_0(D_2172),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2173,'#skF_4','#skF_5',D_2172,'#skF_8'))
      | ~ l1_pre_topc(D_2172)
      | ~ v2_pre_topc(D_2172)
      | v2_struct_0(D_2172)
      | ~ m1_pre_topc(D_2172,A_2173)
      | ~ m1_pre_topc('#skF_5',A_2173)
      | ~ l1_pre_topc(A_2173)
      | ~ v2_pre_topc(A_2173)
      | v2_struct_0(A_2173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_26498])).

tff(c_26527,plain,(
    ! [A_2173] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ v1_funct_2(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_2173)
      | ~ m1_pre_topc('#skF_5',A_2173)
      | ~ l1_pre_topc(A_2173)
      | ~ v2_pre_topc(A_2173)
      | v2_struct_0(A_2173)
      | ~ m1_subset_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21825,c_26501])).

tff(c_26548,plain,(
    ! [A_2173] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_2173)
      | ~ m1_pre_topc('#skF_5',A_2173)
      | ~ l1_pre_topc(A_2173)
      | ~ v2_pre_topc(A_2173)
      | v2_struct_0(A_2173)
      | ~ m1_subset_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_26527])).

tff(c_26549,plain,(
    ! [A_2173] :
      ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
      | ~ m1_pre_topc('#skF_3',A_2173)
      | ~ m1_pre_topc('#skF_5',A_2173)
      | ~ l1_pre_topc(A_2173)
      | ~ v2_pre_topc(A_2173)
      | v2_struct_0(A_2173)
      | ~ m1_subset_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
      | ~ v1_funct_2(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1(A_2173,'#skF_4','#skF_5','#skF_3','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_26548])).

tff(c_31231,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8')) = k2_tmap_1('#skF_3','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8'),'#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8'),k1_zfmisc_1('#skF_9'))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_4','#skF_5','#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31209,c_26549])).

tff(c_31284,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_31209,c_101,c_3902,c_31209,c_86,c_84,c_74,c_99,c_31209,c_31209,c_31231])).

tff(c_31285,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_31284])).

tff(c_31582,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31285,c_17616])).

tff(c_31584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17932,c_31582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:18:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.03/5.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/5.40  
% 13.12/5.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/5.40  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 13.12/5.40  
% 13.12/5.40  %Foreground sorts:
% 13.12/5.40  
% 13.12/5.40  
% 13.12/5.40  %Background operators:
% 13.12/5.40  
% 13.12/5.40  
% 13.12/5.40  %Foreground operators:
% 13.12/5.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.12/5.40  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 13.12/5.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.12/5.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.12/5.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.12/5.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.12/5.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.12/5.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.12/5.40  tff('#skF_7', type, '#skF_7': $i).
% 13.12/5.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.12/5.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.12/5.40  tff('#skF_5', type, '#skF_5': $i).
% 13.12/5.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.12/5.40  tff('#skF_6', type, '#skF_6': $i).
% 13.12/5.40  tff('#skF_3', type, '#skF_3': $i).
% 13.12/5.40  tff('#skF_9', type, '#skF_9': $i).
% 13.12/5.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.12/5.40  tff('#skF_8', type, '#skF_8': $i).
% 13.12/5.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.12/5.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.12/5.40  tff('#skF_4', type, '#skF_4': $i).
% 13.12/5.40  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 13.12/5.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.12/5.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.12/5.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.12/5.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.12/5.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.12/5.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 13.12/5.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.12/5.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.12/5.40  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 13.12/5.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.12/5.40  
% 13.12/5.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.12/5.44  tff(f_263, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 13.12/5.44  tff(f_67, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.12/5.44  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 13.12/5.44  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 13.12/5.44  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 13.12/5.44  tff(f_49, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 13.12/5.44  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 13.12/5.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.12/5.44  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.12/5.44  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 13.12/5.44  tff(f_194, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 13.12/5.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.12/5.44  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_182, plain, (![C_237, B_238, A_239]: (v1_xboole_0(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(B_238, A_239))) | ~v1_xboole_0(A_239))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.12/5.44  tff(c_196, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_182])).
% 13.12/5.44  tff(c_202, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_196])).
% 13.12/5.44  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_66, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_50, plain, ('#skF_6'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_54, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_101, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 13.12/5.44  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_102, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 13.12/5.44  tff(c_48, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_103, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 13.12/5.44  tff(c_3411, plain, (![C_951, D_952, E_953, A_955, B_954, F_950]: (F_950=E_953 | ~r1_funct_2(A_955, B_954, C_951, D_952, E_953, F_950) | ~m1_subset_1(F_950, k1_zfmisc_1(k2_zfmisc_1(C_951, D_952))) | ~v1_funct_2(F_950, C_951, D_952) | ~v1_funct_1(F_950) | ~m1_subset_1(E_953, k1_zfmisc_1(k2_zfmisc_1(A_955, B_954))) | ~v1_funct_2(E_953, A_955, B_954) | ~v1_funct_1(E_953) | v1_xboole_0(D_952) | v1_xboole_0(B_954))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.12/5.44  tff(c_3415, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_103, c_3411])).
% 13.12/5.44  tff(c_3423, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_56, c_101, c_102, c_3415])).
% 13.12/5.44  tff(c_3424, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_202, c_3423])).
% 13.12/5.44  tff(c_1787, plain, (![E_588, F_585, C_586, A_590, D_587, B_589]: (F_585=E_588 | ~r1_funct_2(A_590, B_589, C_586, D_587, E_588, F_585) | ~m1_subset_1(F_585, k1_zfmisc_1(k2_zfmisc_1(C_586, D_587))) | ~v1_funct_2(F_585, C_586, D_587) | ~v1_funct_1(F_585) | ~m1_subset_1(E_588, k1_zfmisc_1(k2_zfmisc_1(A_590, B_589))) | ~v1_funct_2(E_588, A_590, B_589) | ~v1_funct_1(E_588) | v1_xboole_0(D_587) | v1_xboole_0(B_589))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.12/5.44  tff(c_1789, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_103, c_1787])).
% 13.12/5.44  tff(c_1792, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_56, c_101, c_102, c_1789])).
% 13.12/5.44  tff(c_1793, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_202, c_1792])).
% 13.12/5.44  tff(c_96, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_98, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_96])).
% 13.12/5.44  tff(c_316, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_98])).
% 13.12/5.44  tff(c_1795, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1793, c_316])).
% 13.12/5.44  tff(c_74, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_88, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_86, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_84, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_70, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_99, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_70])).
% 13.12/5.44  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_80, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_1993, plain, (![C_648, E_649, B_647, A_646, D_650]: (k3_tmap_1(A_646, B_647, C_648, D_650, E_649)=k2_partfun1(u1_struct_0(C_648), u1_struct_0(B_647), E_649, u1_struct_0(D_650)) | ~m1_pre_topc(D_650, C_648) | ~m1_subset_1(E_649, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_648), u1_struct_0(B_647)))) | ~v1_funct_2(E_649, u1_struct_0(C_648), u1_struct_0(B_647)) | ~v1_funct_1(E_649) | ~m1_pre_topc(D_650, A_646) | ~m1_pre_topc(C_648, A_646) | ~l1_pre_topc(B_647) | ~v2_pre_topc(B_647) | v2_struct_0(B_647) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.12/5.44  tff(c_2002, plain, (![A_646, D_650]: (k3_tmap_1(A_646, '#skF_4', '#skF_3', D_650, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_650)) | ~m1_pre_topc(D_650, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_650, A_646) | ~m1_pre_topc('#skF_3', A_646) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(resolution, [status(thm)], [c_102, c_1993])).
% 13.12/5.44  tff(c_2011, plain, (![A_646, D_650]: (k3_tmap_1(A_646, '#skF_4', '#skF_3', D_650, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_650)) | ~m1_pre_topc(D_650, '#skF_3') | ~m1_pre_topc(D_650, A_646) | ~m1_pre_topc('#skF_3', A_646) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_56, c_101, c_2002])).
% 13.12/5.44  tff(c_2013, plain, (![A_651, D_652]: (k3_tmap_1(A_651, '#skF_4', '#skF_3', D_652, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_652)) | ~m1_pre_topc(D_652, '#skF_3') | ~m1_pre_topc(D_652, A_651) | ~m1_pre_topc('#skF_3', A_651) | ~l1_pre_topc(A_651) | ~v2_pre_topc(A_651) | v2_struct_0(A_651))), inference(negUnitSimplification, [status(thm)], [c_82, c_2011])).
% 13.12/5.44  tff(c_2017, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2013])).
% 13.12/5.44  tff(c_2025, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_74, c_2017])).
% 13.12/5.44  tff(c_2026, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_2025])).
% 13.12/5.44  tff(c_1928, plain, (![A_627, B_628, C_629, D_630]: (k2_partfun1(u1_struct_0(A_627), u1_struct_0(B_628), C_629, u1_struct_0(D_630))=k2_tmap_1(A_627, B_628, C_629, D_630) | ~m1_pre_topc(D_630, A_627) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_627), u1_struct_0(B_628)))) | ~v1_funct_2(C_629, u1_struct_0(A_627), u1_struct_0(B_628)) | ~v1_funct_1(C_629) | ~l1_pre_topc(B_628) | ~v2_pre_topc(B_628) | v2_struct_0(B_628) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.12/5.44  tff(c_1935, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_630))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_630) | ~m1_pre_topc(D_630, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_102, c_1928])).
% 13.12/5.44  tff(c_1943, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_630))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_630) | ~m1_pre_topc(D_630, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_56, c_101, c_1935])).
% 13.12/5.44  tff(c_1944, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_630))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_630) | ~m1_pre_topc(D_630, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_1943])).
% 13.12/5.44  tff(c_2034, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2026, c_1944])).
% 13.12/5.44  tff(c_2041, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2034])).
% 13.12/5.44  tff(c_90, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_100, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_90])).
% 13.12/5.44  tff(c_376, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_100])).
% 13.12/5.44  tff(c_2046, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2041, c_376])).
% 13.12/5.44  tff(c_2049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1795, c_2046])).
% 13.12/5.44  tff(c_2051, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_98])).
% 13.12/5.44  tff(c_3425, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_2051])).
% 13.12/5.44  tff(c_3638, plain, (![A_1013, E_1016, B_1014, D_1017, C_1015]: (k3_tmap_1(A_1013, B_1014, C_1015, D_1017, E_1016)=k2_partfun1(u1_struct_0(C_1015), u1_struct_0(B_1014), E_1016, u1_struct_0(D_1017)) | ~m1_pre_topc(D_1017, C_1015) | ~m1_subset_1(E_1016, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1015), u1_struct_0(B_1014)))) | ~v1_funct_2(E_1016, u1_struct_0(C_1015), u1_struct_0(B_1014)) | ~v1_funct_1(E_1016) | ~m1_pre_topc(D_1017, A_1013) | ~m1_pre_topc(C_1015, A_1013) | ~l1_pre_topc(B_1014) | ~v2_pre_topc(B_1014) | v2_struct_0(B_1014) | ~l1_pre_topc(A_1013) | ~v2_pre_topc(A_1013) | v2_struct_0(A_1013))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.12/5.44  tff(c_3647, plain, (![A_1013, D_1017]: (k3_tmap_1(A_1013, '#skF_4', '#skF_3', D_1017, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_1017)) | ~m1_pre_topc(D_1017, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_1017, A_1013) | ~m1_pre_topc('#skF_3', A_1013) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1013) | ~v2_pre_topc(A_1013) | v2_struct_0(A_1013))), inference(resolution, [status(thm)], [c_102, c_3638])).
% 13.12/5.44  tff(c_3656, plain, (![A_1013, D_1017]: (k3_tmap_1(A_1013, '#skF_4', '#skF_3', D_1017, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_1017)) | ~m1_pre_topc(D_1017, '#skF_3') | ~m1_pre_topc(D_1017, A_1013) | ~m1_pre_topc('#skF_3', A_1013) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1013) | ~v2_pre_topc(A_1013) | v2_struct_0(A_1013))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_56, c_101, c_3647])).
% 13.12/5.44  tff(c_3680, plain, (![A_1020, D_1021]: (k3_tmap_1(A_1020, '#skF_4', '#skF_3', D_1021, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_1021)) | ~m1_pre_topc(D_1021, '#skF_3') | ~m1_pre_topc(D_1021, A_1020) | ~m1_pre_topc('#skF_3', A_1020) | ~l1_pre_topc(A_1020) | ~v2_pre_topc(A_1020) | v2_struct_0(A_1020))), inference(negUnitSimplification, [status(thm)], [c_82, c_3656])).
% 13.12/5.44  tff(c_3684, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3680])).
% 13.12/5.44  tff(c_3692, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_74, c_3684])).
% 13.12/5.44  tff(c_3693, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_3692])).
% 13.12/5.44  tff(c_3557, plain, (![A_991, B_992, C_993, D_994]: (k2_partfun1(u1_struct_0(A_991), u1_struct_0(B_992), C_993, u1_struct_0(D_994))=k2_tmap_1(A_991, B_992, C_993, D_994) | ~m1_pre_topc(D_994, A_991) | ~m1_subset_1(C_993, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_991), u1_struct_0(B_992)))) | ~v1_funct_2(C_993, u1_struct_0(A_991), u1_struct_0(B_992)) | ~v1_funct_1(C_993) | ~l1_pre_topc(B_992) | ~v2_pre_topc(B_992) | v2_struct_0(B_992) | ~l1_pre_topc(A_991) | ~v2_pre_topc(A_991) | v2_struct_0(A_991))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.12/5.44  tff(c_3564, plain, (![D_994]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_994))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_994) | ~m1_pre_topc(D_994, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_102, c_3557])).
% 13.12/5.44  tff(c_3572, plain, (![D_994]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_994))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_994) | ~m1_pre_topc(D_994, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_56, c_101, c_3564])).
% 13.12/5.44  tff(c_3573, plain, (![D_994]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_994))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_994) | ~m1_pre_topc(D_994, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_3572])).
% 13.12/5.44  tff(c_3701, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3693, c_3573])).
% 13.12/5.44  tff(c_3708, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3701])).
% 13.12/5.44  tff(c_2050, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_98])).
% 13.12/5.44  tff(c_3714, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3708, c_2050])).
% 13.12/5.44  tff(c_3716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3425, c_3714])).
% 13.12/5.44  tff(c_3717, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_196])).
% 13.12/5.44  tff(c_20, plain, (![A_13]: (~v1_xboole_0(k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.12/5.44  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(k1_tarski(A_14), k1_zfmisc_1(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.12/5.44  tff(c_189, plain, (![A_14, A_239, B_238]: (v1_xboole_0(k1_tarski(A_14)) | ~v1_xboole_0(A_239) | ~r2_hidden(A_14, k2_zfmisc_1(B_238, A_239)))), inference(resolution, [status(thm)], [c_22, c_182])).
% 13.12/5.44  tff(c_3800, plain, (![A_1029, A_1030, B_1031]: (~v1_xboole_0(A_1029) | ~r2_hidden(A_1030, k2_zfmisc_1(B_1031, A_1029)))), inference(negUnitSimplification, [status(thm)], [c_20, c_189])).
% 13.12/5.44  tff(c_3811, plain, (![A_1032, B_1033]: (~v1_xboole_0(A_1032) | v1_xboole_0(k2_zfmisc_1(B_1033, A_1032)))), inference(resolution, [status(thm)], [c_4, c_3800])).
% 13.12/5.44  tff(c_3718, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_196])).
% 13.12/5.44  tff(c_127, plain, (![A_219, B_220]: (r2_hidden('#skF_2'(A_219, B_220), A_219) | r1_tarski(A_219, B_220))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.12/5.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.12/5.44  tff(c_131, plain, (![A_219, B_220]: (~v1_xboole_0(A_219) | r1_tarski(A_219, B_220))), inference(resolution, [status(thm)], [c_127, c_2])).
% 13.12/5.44  tff(c_140, plain, (![B_225, A_226]: (B_225=A_226 | ~r1_tarski(B_225, A_226) | ~r1_tarski(A_226, B_225))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.12/5.44  tff(c_150, plain, (![B_227, A_228]: (B_227=A_228 | ~r1_tarski(B_227, A_228) | ~v1_xboole_0(A_228))), inference(resolution, [status(thm)], [c_131, c_140])).
% 13.12/5.44  tff(c_157, plain, (![B_220, A_219]: (B_220=A_219 | ~v1_xboole_0(B_220) | ~v1_xboole_0(A_219))), inference(resolution, [status(thm)], [c_131, c_150])).
% 13.12/5.44  tff(c_3732, plain, (![A_1025]: (A_1025='#skF_8' | ~v1_xboole_0(A_1025))), inference(resolution, [status(thm)], [c_3717, c_157])).
% 13.12/5.44  tff(c_3739, plain, (u1_struct_0('#skF_4')='#skF_8'), inference(resolution, [status(thm)], [c_3718, c_3732])).
% 13.12/5.44  tff(c_161, plain, (![C_231, B_232, A_233]: (~v1_xboole_0(C_231) | ~m1_subset_1(B_232, k1_zfmisc_1(C_231)) | ~r2_hidden(A_233, B_232))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.12/5.44  tff(c_172, plain, (![A_233]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))) | ~r2_hidden(A_233, '#skF_9'))), inference(resolution, [status(thm)], [c_102, c_161])).
% 13.12/5.44  tff(c_181, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_172])).
% 13.12/5.44  tff(c_3799, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3739, c_181])).
% 13.12/5.44  tff(c_3814, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_3811, c_3799])).
% 13.12/5.44  tff(c_3823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3717, c_3814])).
% 13.12/5.44  tff(c_3826, plain, (![A_1034]: (~r2_hidden(A_1034, '#skF_9'))), inference(splitRight, [status(thm)], [c_172])).
% 13.12/5.44  tff(c_3836, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_3826])).
% 13.12/5.44  tff(c_3825, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_172])).
% 13.12/5.44  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.12/5.44  tff(c_3861, plain, (![B_1038]: (r1_tarski('#skF_9', B_1038))), inference(resolution, [status(thm)], [c_10, c_3826])).
% 13.12/5.44  tff(c_145, plain, (![B_220, A_219]: (B_220=A_219 | ~r1_tarski(B_220, A_219) | ~v1_xboole_0(A_219))), inference(resolution, [status(thm)], [c_131, c_140])).
% 13.12/5.44  tff(c_3867, plain, (![B_1038]: (B_1038='#skF_9' | ~v1_xboole_0(B_1038))), inference(resolution, [status(thm)], [c_3861, c_145])).
% 13.12/5.44  tff(c_3899, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_9'), inference(resolution, [status(thm)], [c_3825, c_3867])).
% 13.12/5.44  tff(c_3903, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3899, c_64])).
% 13.12/5.44  tff(c_24, plain, (![C_18, B_17, A_16]: (~v1_xboole_0(C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(C_18)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.12/5.44  tff(c_3925, plain, (![A_16]: (~v1_xboole_0('#skF_9') | ~r2_hidden(A_16, '#skF_7'))), inference(resolution, [status(thm)], [c_3903, c_24])).
% 13.12/5.44  tff(c_3929, plain, (![A_1044]: (~r2_hidden(A_1044, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3836, c_3925])).
% 13.12/5.44  tff(c_3939, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_3929])).
% 13.12/5.44  tff(c_3947, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_3939, c_3867])).
% 13.12/5.44  tff(c_4080, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3947, c_98])).
% 13.12/5.44  tff(c_4081, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_4080])).
% 13.12/5.44  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_60, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 13.12/5.44  tff(c_6656, plain, (![A_1264, C_1265, D_1263, E_1267, B_1266]: (m1_subset_1(k3_tmap_1(A_1264, B_1266, C_1265, D_1263, E_1267), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1263), u1_struct_0(B_1266)))) | ~m1_subset_1(E_1267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265), u1_struct_0(B_1266)))) | ~v1_funct_2(E_1267, u1_struct_0(C_1265), u1_struct_0(B_1266)) | ~v1_funct_1(E_1267) | ~m1_pre_topc(D_1263, A_1264) | ~m1_pre_topc(C_1265, A_1264) | ~l1_pre_topc(B_1266) | ~v2_pre_topc(B_1266) | v2_struct_0(B_1266) | ~l1_pre_topc(A_1264) | ~v2_pre_topc(A_1264) | v2_struct_0(A_1264))), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.12/5.44  tff(c_6674, plain, (![A_1264, C_1265, E_1267]: (m1_subset_1(k3_tmap_1(A_1264, '#skF_4', C_1265, '#skF_3', E_1267), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1267, u1_struct_0(C_1265), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1267) | ~m1_pre_topc('#skF_3', A_1264) | ~m1_pre_topc(C_1265, A_1264) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1264) | ~v2_pre_topc(A_1264) | v2_struct_0(A_1264))), inference(superposition, [status(thm), theory('equality')], [c_3899, c_6656])).
% 13.12/5.44  tff(c_6683, plain, (![A_1264, C_1265, E_1267]: (m1_subset_1(k3_tmap_1(A_1264, '#skF_4', C_1265, '#skF_3', E_1267), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1265), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1267, u1_struct_0(C_1265), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1267) | ~m1_pre_topc('#skF_3', A_1264) | ~m1_pre_topc(C_1265, A_1264) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1264) | ~v2_pre_topc(A_1264) | v2_struct_0(A_1264))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_6674])).
% 13.12/5.44  tff(c_8770, plain, (![A_1353, C_1354, E_1355]: (m1_subset_1(k3_tmap_1(A_1353, '#skF_4', C_1354, '#skF_3', E_1355), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1354), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1355, u1_struct_0(C_1354), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1355) | ~m1_pre_topc('#skF_3', A_1353) | ~m1_pre_topc(C_1354, A_1353) | ~l1_pre_topc(A_1353) | ~v2_pre_topc(A_1353) | v2_struct_0(A_1353))), inference(negUnitSimplification, [status(thm)], [c_82, c_6683])).
% 13.12/5.44  tff(c_8777, plain, (![A_1353]: (m1_subset_1(k3_tmap_1(A_1353, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_3', A_1353) | ~m1_pre_topc('#skF_5', A_1353) | ~l1_pre_topc(A_1353) | ~v2_pre_topc(A_1353) | v2_struct_0(A_1353))), inference(resolution, [status(thm)], [c_58, c_8770])).
% 13.12/5.44  tff(c_17299, plain, (![A_1626]: (m1_subset_1(k3_tmap_1(A_1626, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~m1_pre_topc('#skF_3', A_1626) | ~m1_pre_topc('#skF_5', A_1626) | ~l1_pre_topc(A_1626) | ~v2_pre_topc(A_1626) | v2_struct_0(A_1626))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8777])).
% 13.12/5.44  tff(c_3840, plain, (![C_1035, B_1036, A_1037]: (v1_xboole_0(C_1035) | ~m1_subset_1(C_1035, k1_zfmisc_1(k2_zfmisc_1(B_1036, A_1037))) | ~v1_xboole_0(A_1037))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.12/5.44  tff(c_3847, plain, (![A_14, A_1037, B_1036]: (v1_xboole_0(k1_tarski(A_14)) | ~v1_xboole_0(A_1037) | ~r2_hidden(A_14, k2_zfmisc_1(B_1036, A_1037)))), inference(resolution, [status(thm)], [c_22, c_3840])).
% 13.12/5.44  tff(c_3965, plain, (![A_1045, A_1046, B_1047]: (~v1_xboole_0(A_1045) | ~r2_hidden(A_1046, k2_zfmisc_1(B_1047, A_1045)))), inference(negUnitSimplification, [status(thm)], [c_20, c_3847])).
% 13.12/5.44  tff(c_3991, plain, (![A_1051, B_1052]: (~v1_xboole_0(A_1051) | v1_xboole_0(k2_zfmisc_1(B_1052, A_1051)))), inference(resolution, [status(thm)], [c_4, c_3965])).
% 13.12/5.44  tff(c_4003, plain, (![B_1053, A_1054]: (k2_zfmisc_1(B_1053, A_1054)='#skF_9' | ~v1_xboole_0(A_1054))), inference(resolution, [status(thm)], [c_3991, c_3867])).
% 13.12/5.44  tff(c_4010, plain, (![B_1055]: (k2_zfmisc_1(B_1055, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_3836, c_4003])).
% 13.12/5.44  tff(c_26, plain, (![C_22, B_20, A_19]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.12/5.44  tff(c_4023, plain, (![C_22]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1('#skF_9')) | ~v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4010, c_26])).
% 13.12/5.44  tff(c_4032, plain, (![C_22]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3836, c_4023])).
% 13.12/5.44  tff(c_17312, plain, (![A_1627]: (v1_xboole_0(k3_tmap_1(A_1627, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~m1_pre_topc('#skF_3', A_1627) | ~m1_pre_topc('#skF_5', A_1627) | ~l1_pre_topc(A_1627) | ~v2_pre_topc(A_1627) | v2_struct_0(A_1627))), inference(resolution, [status(thm)], [c_17299, c_4032])).
% 13.12/5.44  tff(c_17359, plain, (![A_1628]: (k3_tmap_1(A_1628, '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | ~m1_pre_topc('#skF_3', A_1628) | ~m1_pre_topc('#skF_5', A_1628) | ~l1_pre_topc(A_1628) | ~v2_pre_topc(A_1628) | v2_struct_0(A_1628))), inference(resolution, [status(thm)], [c_17312, c_3867])).
% 13.12/5.44  tff(c_17365, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_17359])).
% 13.12/5.44  tff(c_17369, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_17365])).
% 13.12/5.44  tff(c_17370, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_88, c_17369])).
% 13.12/5.44  tff(c_3902, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3899, c_102])).
% 13.12/5.44  tff(c_36, plain, (![A_33, B_41, C_45, D_47]: (k2_partfun1(u1_struct_0(A_33), u1_struct_0(B_41), C_45, u1_struct_0(D_47))=k2_tmap_1(A_33, B_41, C_45, D_47) | ~m1_pre_topc(D_47, A_33) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33), u1_struct_0(B_41)))) | ~v1_funct_2(C_45, u1_struct_0(A_33), u1_struct_0(B_41)) | ~v1_funct_1(C_45) | ~l1_pre_topc(B_41) | ~v2_pre_topc(B_41) | v2_struct_0(B_41) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.12/5.44  tff(c_14237, plain, (![E_1564, C_1561, D_1560, B_1562, D_1559, A_1563]: (k2_partfun1(u1_struct_0(D_1559), u1_struct_0(B_1562), k3_tmap_1(A_1563, B_1562, C_1561, D_1559, E_1564), u1_struct_0(D_1560))=k2_tmap_1(D_1559, B_1562, k3_tmap_1(A_1563, B_1562, C_1561, D_1559, E_1564), D_1560) | ~m1_pre_topc(D_1560, D_1559) | ~v1_funct_2(k3_tmap_1(A_1563, B_1562, C_1561, D_1559, E_1564), u1_struct_0(D_1559), u1_struct_0(B_1562)) | ~v1_funct_1(k3_tmap_1(A_1563, B_1562, C_1561, D_1559, E_1564)) | ~l1_pre_topc(D_1559) | ~v2_pre_topc(D_1559) | v2_struct_0(D_1559) | ~m1_subset_1(E_1564, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1561), u1_struct_0(B_1562)))) | ~v1_funct_2(E_1564, u1_struct_0(C_1561), u1_struct_0(B_1562)) | ~v1_funct_1(E_1564) | ~m1_pre_topc(D_1559, A_1563) | ~m1_pre_topc(C_1561, A_1563) | ~l1_pre_topc(B_1562) | ~v2_pre_topc(B_1562) | v2_struct_0(B_1562) | ~l1_pre_topc(A_1563) | ~v2_pre_topc(A_1563) | v2_struct_0(A_1563))), inference(resolution, [status(thm)], [c_6656, c_36])).
% 13.12/5.44  tff(c_14243, plain, (![D_1559, A_1563, D_1560]: (k2_partfun1(u1_struct_0(D_1559), u1_struct_0('#skF_4'), k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), u1_struct_0(D_1560))=k2_tmap_1(D_1559, '#skF_4', k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), D_1560) | ~m1_pre_topc(D_1560, D_1559) | ~v1_funct_2(k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), u1_struct_0(D_1559), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8')) | ~l1_pre_topc(D_1559) | ~v2_pre_topc(D_1559) | v2_struct_0(D_1559) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_1559, A_1563) | ~m1_pre_topc('#skF_5', A_1563) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1563) | ~v2_pre_topc(A_1563) | v2_struct_0(A_1563))), inference(resolution, [status(thm)], [c_58, c_14237])).
% 13.12/5.44  tff(c_14253, plain, (![D_1559, A_1563, D_1560]: (k2_partfun1(u1_struct_0(D_1559), u1_struct_0('#skF_4'), k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), u1_struct_0(D_1560))=k2_tmap_1(D_1559, '#skF_4', k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), D_1560) | ~m1_pre_topc(D_1560, D_1559) | ~v1_funct_2(k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8'), u1_struct_0(D_1559), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1563, '#skF_4', '#skF_5', D_1559, '#skF_8')) | ~l1_pre_topc(D_1559) | ~v2_pre_topc(D_1559) | v2_struct_0(D_1559) | ~m1_pre_topc(D_1559, A_1563) | ~m1_pre_topc('#skF_5', A_1563) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1563) | ~v2_pre_topc(A_1563) | v2_struct_0(A_1563))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_60, c_14243])).
% 13.12/5.44  tff(c_14256, plain, (![D_1565, A_1566, D_1567]: (k2_partfun1(u1_struct_0(D_1565), u1_struct_0('#skF_4'), k3_tmap_1(A_1566, '#skF_4', '#skF_5', D_1565, '#skF_8'), u1_struct_0(D_1567))=k2_tmap_1(D_1565, '#skF_4', k3_tmap_1(A_1566, '#skF_4', '#skF_5', D_1565, '#skF_8'), D_1567) | ~m1_pre_topc(D_1567, D_1565) | ~v1_funct_2(k3_tmap_1(A_1566, '#skF_4', '#skF_5', D_1565, '#skF_8'), u1_struct_0(D_1565), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', D_1565, '#skF_8')) | ~l1_pre_topc(D_1565) | ~v2_pre_topc(D_1565) | v2_struct_0(D_1565) | ~m1_pre_topc(D_1565, A_1566) | ~m1_pre_topc('#skF_5', A_1566) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(negUnitSimplification, [status(thm)], [c_82, c_14253])).
% 13.12/5.44  tff(c_7103, plain, (![B_1283, E_1285, A_1282, C_1284, D_1286]: (k3_tmap_1(A_1282, B_1283, C_1284, D_1286, E_1285)=k2_partfun1(u1_struct_0(C_1284), u1_struct_0(B_1283), E_1285, u1_struct_0(D_1286)) | ~m1_pre_topc(D_1286, C_1284) | ~m1_subset_1(E_1285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1284), u1_struct_0(B_1283)))) | ~v1_funct_2(E_1285, u1_struct_0(C_1284), u1_struct_0(B_1283)) | ~v1_funct_1(E_1285) | ~m1_pre_topc(D_1286, A_1282) | ~m1_pre_topc(C_1284, A_1282) | ~l1_pre_topc(B_1283) | ~v2_pre_topc(B_1283) | v2_struct_0(B_1283) | ~l1_pre_topc(A_1282) | ~v2_pre_topc(A_1282) | v2_struct_0(A_1282))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.12/5.44  tff(c_7107, plain, (![A_1282, D_1286, E_1285]: (k3_tmap_1(A_1282, '#skF_4', '#skF_3', D_1286, E_1285)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1285, u1_struct_0(D_1286)) | ~m1_pre_topc(D_1286, '#skF_3') | ~m1_subset_1(E_1285, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1285, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1285) | ~m1_pre_topc(D_1286, A_1282) | ~m1_pre_topc('#skF_3', A_1282) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1282) | ~v2_pre_topc(A_1282) | v2_struct_0(A_1282))), inference(superposition, [status(thm), theory('equality')], [c_3899, c_7103])).
% 13.12/5.44  tff(c_7115, plain, (![A_1282, D_1286, E_1285]: (k3_tmap_1(A_1282, '#skF_4', '#skF_3', D_1286, E_1285)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1285, u1_struct_0(D_1286)) | ~m1_pre_topc(D_1286, '#skF_3') | ~m1_subset_1(E_1285, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1285, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1285) | ~m1_pre_topc(D_1286, A_1282) | ~m1_pre_topc('#skF_3', A_1282) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1282) | ~v2_pre_topc(A_1282) | v2_struct_0(A_1282))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_7107])).
% 13.12/5.44  tff(c_9783, plain, (![A_1375, D_1376, E_1377]: (k3_tmap_1(A_1375, '#skF_4', '#skF_3', D_1376, E_1377)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1377, u1_struct_0(D_1376)) | ~m1_pre_topc(D_1376, '#skF_3') | ~m1_subset_1(E_1377, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1377, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1377) | ~m1_pre_topc(D_1376, A_1375) | ~m1_pre_topc('#skF_3', A_1375) | ~l1_pre_topc(A_1375) | ~v2_pre_topc(A_1375) | v2_struct_0(A_1375))), inference(negUnitSimplification, [status(thm)], [c_82, c_7115])).
% 13.12/5.44  tff(c_9787, plain, (![E_1377]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1377, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1377) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(E_1377, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1377, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1377) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_9783])).
% 13.12/5.44  tff(c_9795, plain, (![E_1377]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1377, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1377) | ~m1_subset_1(E_1377, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1377, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1377) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_74, c_9787])).
% 13.12/5.44  tff(c_9796, plain, (![E_1377]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1377, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1377) | ~m1_subset_1(E_1377, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1377, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1377))), inference(negUnitSimplification, [status(thm)], [c_88, c_9795])).
% 13.12/5.44  tff(c_14267, plain, (![A_1566]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_subset_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_1566) | ~m1_pre_topc('#skF_5', A_1566) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(superposition, [status(thm), theory('equality')], [c_14256, c_9796])).
% 13.12/5.44  tff(c_14292, plain, (![A_1566]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_subset_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_1566) | ~m1_pre_topc('#skF_5', A_1566) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_14267])).
% 13.12/5.44  tff(c_14293, plain, (![A_1566]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_subset_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_1566, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~m1_pre_topc('#skF_3', A_1566) | ~m1_pre_topc('#skF_5', A_1566) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(negUnitSimplification, [status(thm)], [c_88, c_14292])).
% 13.12/5.44  tff(c_17385, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17370, c_14293])).
% 13.12/5.44  tff(c_17434, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_99, c_56, c_17370, c_101, c_3902, c_17370, c_17370, c_17370, c_17385])).
% 13.12/5.44  tff(c_17435, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_88, c_17434])).
% 13.12/5.44  tff(c_4229, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3947, c_100])).
% 13.12/5.44  tff(c_4230, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_4229])).
% 13.12/5.44  tff(c_17486, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17435, c_4230])).
% 13.12/5.44  tff(c_17489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4081, c_17486])).
% 13.12/5.44  tff(c_17490, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_4229])).
% 13.12/5.44  tff(c_17615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17490, c_4081])).
% 13.12/5.44  tff(c_17616, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_4080])).
% 13.12/5.44  tff(c_17706, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3947, c_100])).
% 13.12/5.44  tff(c_17707, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_17706])).
% 13.12/5.44  tff(c_17931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17616, c_17707])).
% 13.12/5.44  tff(c_17932, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_17706])).
% 13.12/5.44  tff(c_20235, plain, (![A_1883, E_1886, B_1885, D_1882, C_1884]: (m1_subset_1(k3_tmap_1(A_1883, B_1885, C_1884, D_1882, E_1886), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1882), u1_struct_0(B_1885)))) | ~m1_subset_1(E_1886, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884), u1_struct_0(B_1885)))) | ~v1_funct_2(E_1886, u1_struct_0(C_1884), u1_struct_0(B_1885)) | ~v1_funct_1(E_1886) | ~m1_pre_topc(D_1882, A_1883) | ~m1_pre_topc(C_1884, A_1883) | ~l1_pre_topc(B_1885) | ~v2_pre_topc(B_1885) | v2_struct_0(B_1885) | ~l1_pre_topc(A_1883) | ~v2_pre_topc(A_1883) | v2_struct_0(A_1883))), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.12/5.44  tff(c_20253, plain, (![A_1883, C_1884, E_1886]: (m1_subset_1(k3_tmap_1(A_1883, '#skF_4', C_1884, '#skF_3', E_1886), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1886, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1886, u1_struct_0(C_1884), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1886) | ~m1_pre_topc('#skF_3', A_1883) | ~m1_pre_topc(C_1884, A_1883) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1883) | ~v2_pre_topc(A_1883) | v2_struct_0(A_1883))), inference(superposition, [status(thm), theory('equality')], [c_3899, c_20235])).
% 13.12/5.44  tff(c_20262, plain, (![A_1883, C_1884, E_1886]: (m1_subset_1(k3_tmap_1(A_1883, '#skF_4', C_1884, '#skF_3', E_1886), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1886, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1884), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1886, u1_struct_0(C_1884), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1886) | ~m1_pre_topc('#skF_3', A_1883) | ~m1_pre_topc(C_1884, A_1883) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1883) | ~v2_pre_topc(A_1883) | v2_struct_0(A_1883))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_20253])).
% 13.12/5.44  tff(c_21774, plain, (![A_1977, C_1978, E_1979]: (m1_subset_1(k3_tmap_1(A_1977, '#skF_4', C_1978, '#skF_3', E_1979), k1_zfmisc_1('#skF_9')) | ~m1_subset_1(E_1979, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1978), u1_struct_0('#skF_4')))) | ~v1_funct_2(E_1979, u1_struct_0(C_1978), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1979) | ~m1_pre_topc('#skF_3', A_1977) | ~m1_pre_topc(C_1978, A_1977) | ~l1_pre_topc(A_1977) | ~v2_pre_topc(A_1977) | v2_struct_0(A_1977))), inference(negUnitSimplification, [status(thm)], [c_82, c_20262])).
% 13.12/5.44  tff(c_21781, plain, (![A_1977]: (m1_subset_1(k3_tmap_1(A_1977, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_3', A_1977) | ~m1_pre_topc('#skF_5', A_1977) | ~l1_pre_topc(A_1977) | ~v2_pre_topc(A_1977) | v2_struct_0(A_1977))), inference(resolution, [status(thm)], [c_58, c_21774])).
% 13.12/5.44  tff(c_31028, plain, (![A_2261]: (m1_subset_1(k3_tmap_1(A_2261, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~m1_pre_topc('#skF_3', A_2261) | ~m1_pre_topc('#skF_5', A_2261) | ~l1_pre_topc(A_2261) | ~v2_pre_topc(A_2261) | v2_struct_0(A_2261))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_21781])).
% 13.12/5.44  tff(c_31151, plain, (![A_2266]: (v1_xboole_0(k3_tmap_1(A_2266, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~m1_pre_topc('#skF_3', A_2266) | ~m1_pre_topc('#skF_5', A_2266) | ~l1_pre_topc(A_2266) | ~v2_pre_topc(A_2266) | v2_struct_0(A_2266))), inference(resolution, [status(thm)], [c_31028, c_4032])).
% 13.12/5.44  tff(c_31198, plain, (![A_2267]: (k3_tmap_1(A_2267, '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | ~m1_pre_topc('#skF_3', A_2267) | ~m1_pre_topc('#skF_5', A_2267) | ~l1_pre_topc(A_2267) | ~v2_pre_topc(A_2267) | v2_struct_0(A_2267))), inference(resolution, [status(thm)], [c_31151, c_3867])).
% 13.12/5.44  tff(c_31204, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_31198])).
% 13.12/5.44  tff(c_31208, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_31204])).
% 13.12/5.44  tff(c_31209, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_88, c_31208])).
% 13.12/5.44  tff(c_20861, plain, (![E_1917, D_1918, C_1916, B_1915, A_1914]: (k3_tmap_1(A_1914, B_1915, C_1916, D_1918, E_1917)=k2_partfun1(u1_struct_0(C_1916), u1_struct_0(B_1915), E_1917, u1_struct_0(D_1918)) | ~m1_pre_topc(D_1918, C_1916) | ~m1_subset_1(E_1917, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1916), u1_struct_0(B_1915)))) | ~v1_funct_2(E_1917, u1_struct_0(C_1916), u1_struct_0(B_1915)) | ~v1_funct_1(E_1917) | ~m1_pre_topc(D_1918, A_1914) | ~m1_pre_topc(C_1916, A_1914) | ~l1_pre_topc(B_1915) | ~v2_pre_topc(B_1915) | v2_struct_0(B_1915) | ~l1_pre_topc(A_1914) | ~v2_pre_topc(A_1914) | v2_struct_0(A_1914))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.12/5.44  tff(c_20865, plain, (![A_1914, D_1918, E_1917]: (k3_tmap_1(A_1914, '#skF_4', '#skF_3', D_1918, E_1917)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1917, u1_struct_0(D_1918)) | ~m1_pre_topc(D_1918, '#skF_3') | ~m1_subset_1(E_1917, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1917, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1917) | ~m1_pre_topc(D_1918, A_1914) | ~m1_pre_topc('#skF_3', A_1914) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1914) | ~v2_pre_topc(A_1914) | v2_struct_0(A_1914))), inference(superposition, [status(thm), theory('equality')], [c_3899, c_20861])).
% 13.12/5.44  tff(c_20873, plain, (![A_1914, D_1918, E_1917]: (k3_tmap_1(A_1914, '#skF_4', '#skF_3', D_1918, E_1917)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1917, u1_struct_0(D_1918)) | ~m1_pre_topc(D_1918, '#skF_3') | ~m1_subset_1(E_1917, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1917, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1917) | ~m1_pre_topc(D_1918, A_1914) | ~m1_pre_topc('#skF_3', A_1914) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1914) | ~v2_pre_topc(A_1914) | v2_struct_0(A_1914))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_20865])).
% 13.12/5.44  tff(c_21812, plain, (![A_1985, D_1986, E_1987]: (k3_tmap_1(A_1985, '#skF_4', '#skF_3', D_1986, E_1987)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1987, u1_struct_0(D_1986)) | ~m1_pre_topc(D_1986, '#skF_3') | ~m1_subset_1(E_1987, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1987, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1987) | ~m1_pre_topc(D_1986, A_1985) | ~m1_pre_topc('#skF_3', A_1985) | ~l1_pre_topc(A_1985) | ~v2_pre_topc(A_1985) | v2_struct_0(A_1985))), inference(negUnitSimplification, [status(thm)], [c_82, c_20873])).
% 13.12/5.44  tff(c_21816, plain, (![E_1987]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1987, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1987) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(E_1987, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1987, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1987) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_21812])).
% 13.12/5.44  tff(c_21824, plain, (![E_1987]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1987, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1987) | ~m1_subset_1(E_1987, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1987, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1987) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_99, c_74, c_21816])).
% 13.12/5.44  tff(c_21825, plain, (![E_1987]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), E_1987, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', E_1987) | ~m1_subset_1(E_1987, k1_zfmisc_1('#skF_9')) | ~v1_funct_2(E_1987, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(E_1987))), inference(negUnitSimplification, [status(thm)], [c_88, c_21824])).
% 13.12/5.44  tff(c_26482, plain, (![D_2166, B_2169, A_2167, D_2170, E_2171, C_2168]: (k2_partfun1(u1_struct_0(D_2170), u1_struct_0(B_2169), k3_tmap_1(A_2167, B_2169, C_2168, D_2170, E_2171), u1_struct_0(D_2166))=k2_tmap_1(D_2170, B_2169, k3_tmap_1(A_2167, B_2169, C_2168, D_2170, E_2171), D_2166) | ~m1_pre_topc(D_2166, D_2170) | ~v1_funct_2(k3_tmap_1(A_2167, B_2169, C_2168, D_2170, E_2171), u1_struct_0(D_2170), u1_struct_0(B_2169)) | ~v1_funct_1(k3_tmap_1(A_2167, B_2169, C_2168, D_2170, E_2171)) | ~l1_pre_topc(D_2170) | ~v2_pre_topc(D_2170) | v2_struct_0(D_2170) | ~m1_subset_1(E_2171, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_2168), u1_struct_0(B_2169)))) | ~v1_funct_2(E_2171, u1_struct_0(C_2168), u1_struct_0(B_2169)) | ~v1_funct_1(E_2171) | ~m1_pre_topc(D_2170, A_2167) | ~m1_pre_topc(C_2168, A_2167) | ~l1_pre_topc(B_2169) | ~v2_pre_topc(B_2169) | v2_struct_0(B_2169) | ~l1_pre_topc(A_2167) | ~v2_pre_topc(A_2167) | v2_struct_0(A_2167))), inference(resolution, [status(thm)], [c_20235, c_36])).
% 13.12/5.44  tff(c_26488, plain, (![D_2170, A_2167, D_2166]: (k2_partfun1(u1_struct_0(D_2170), u1_struct_0('#skF_4'), k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), u1_struct_0(D_2166))=k2_tmap_1(D_2170, '#skF_4', k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), D_2166) | ~m1_pre_topc(D_2166, D_2170) | ~v1_funct_2(k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), u1_struct_0(D_2170), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8')) | ~l1_pre_topc(D_2170) | ~v2_pre_topc(D_2170) | v2_struct_0(D_2170) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_2170, A_2167) | ~m1_pre_topc('#skF_5', A_2167) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_2167) | ~v2_pre_topc(A_2167) | v2_struct_0(A_2167))), inference(resolution, [status(thm)], [c_58, c_26482])).
% 13.12/5.44  tff(c_26498, plain, (![D_2170, A_2167, D_2166]: (k2_partfun1(u1_struct_0(D_2170), u1_struct_0('#skF_4'), k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), u1_struct_0(D_2166))=k2_tmap_1(D_2170, '#skF_4', k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), D_2166) | ~m1_pre_topc(D_2166, D_2170) | ~v1_funct_2(k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8'), u1_struct_0(D_2170), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2167, '#skF_4', '#skF_5', D_2170, '#skF_8')) | ~l1_pre_topc(D_2170) | ~v2_pre_topc(D_2170) | v2_struct_0(D_2170) | ~m1_pre_topc(D_2170, A_2167) | ~m1_pre_topc('#skF_5', A_2167) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_2167) | ~v2_pre_topc(A_2167) | v2_struct_0(A_2167))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_60, c_26488])).
% 13.12/5.44  tff(c_26501, plain, (![D_2172, A_2173, D_2174]: (k2_partfun1(u1_struct_0(D_2172), u1_struct_0('#skF_4'), k3_tmap_1(A_2173, '#skF_4', '#skF_5', D_2172, '#skF_8'), u1_struct_0(D_2174))=k2_tmap_1(D_2172, '#skF_4', k3_tmap_1(A_2173, '#skF_4', '#skF_5', D_2172, '#skF_8'), D_2174) | ~m1_pre_topc(D_2174, D_2172) | ~v1_funct_2(k3_tmap_1(A_2173, '#skF_4', '#skF_5', D_2172, '#skF_8'), u1_struct_0(D_2172), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', D_2172, '#skF_8')) | ~l1_pre_topc(D_2172) | ~v2_pre_topc(D_2172) | v2_struct_0(D_2172) | ~m1_pre_topc(D_2172, A_2173) | ~m1_pre_topc('#skF_5', A_2173) | ~l1_pre_topc(A_2173) | ~v2_pre_topc(A_2173) | v2_struct_0(A_2173))), inference(negUnitSimplification, [status(thm)], [c_82, c_26498])).
% 13.12/5.44  tff(c_26527, plain, (![A_2173]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_2173) | ~m1_pre_topc('#skF_5', A_2173) | ~l1_pre_topc(A_2173) | ~v2_pre_topc(A_2173) | v2_struct_0(A_2173) | ~m1_subset_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_21825, c_26501])).
% 13.12/5.44  tff(c_26548, plain, (![A_2173]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_2173) | ~m1_pre_topc('#skF_5', A_2173) | ~l1_pre_topc(A_2173) | ~v2_pre_topc(A_2173) | v2_struct_0(A_2173) | ~m1_subset_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_26527])).
% 13.12/5.44  tff(c_26549, plain, (![A_2173]: (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_pre_topc('#skF_3', A_2173) | ~m1_pre_topc('#skF_5', A_2173) | ~l1_pre_topc(A_2173) | ~v2_pre_topc(A_2173) | v2_struct_0(A_2173) | ~m1_subset_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1(A_2173, '#skF_4', '#skF_5', '#skF_3', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_88, c_26548])).
% 13.12/5.44  tff(c_31231, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'))=k2_tmap_1('#skF_3', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'), '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'), k1_zfmisc_1('#skF_9')) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_3', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_31209, c_26549])).
% 13.12/5.44  tff(c_31284, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_31209, c_101, c_3902, c_31209, c_86, c_84, c_74, c_99, c_31209, c_31209, c_31231])).
% 13.12/5.44  tff(c_31285, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_88, c_31284])).
% 13.12/5.44  tff(c_31582, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31285, c_17616])).
% 13.12/5.44  tff(c_31584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17932, c_31582])).
% 13.12/5.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/5.44  
% 13.12/5.44  Inference rules
% 13.12/5.44  ----------------------
% 13.12/5.44  #Ref     : 0
% 13.12/5.44  #Sup     : 8503
% 13.12/5.44  #Fact    : 0
% 13.12/5.44  #Define  : 0
% 13.12/5.44  #Split   : 82
% 13.12/5.44  #Chain   : 0
% 13.12/5.44  #Close   : 0
% 13.12/5.44  
% 13.12/5.44  Ordering : KBO
% 13.12/5.44  
% 13.12/5.44  Simplification rules
% 13.12/5.44  ----------------------
% 13.12/5.44  #Subsume      : 5136
% 13.12/5.44  #Demod        : 6151
% 13.12/5.44  #Tautology    : 1235
% 13.12/5.44  #SimpNegUnit  : 461
% 13.12/5.44  #BackRed      : 127
% 13.12/5.44  
% 13.12/5.44  #Partial instantiations: 0
% 13.12/5.44  #Strategies tried      : 1
% 13.12/5.44  
% 13.12/5.44  Timing (in seconds)
% 13.12/5.44  ----------------------
% 13.12/5.44  Preprocessing        : 0.41
% 13.12/5.44  Parsing              : 0.20
% 13.12/5.44  CNF conversion       : 0.05
% 13.12/5.44  Main loop            : 4.23
% 13.12/5.44  Inferencing          : 1.23
% 13.12/5.44  Reduction            : 1.26
% 13.12/5.44  Demodulation         : 0.94
% 13.12/5.44  BG Simplification    : 0.11
% 13.12/5.44  Subsumption          : 1.41
% 13.12/5.44  Abstraction          : 0.18
% 13.12/5.44  MUC search           : 0.00
% 13.12/5.44  Cooper               : 0.00
% 13.12/5.44  Total                : 4.71
% 13.12/5.44  Index Insertion      : 0.00
% 13.12/5.44  Index Deletion       : 0.00
% 13.12/5.44  Index Matching       : 0.00
% 13.12/5.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
