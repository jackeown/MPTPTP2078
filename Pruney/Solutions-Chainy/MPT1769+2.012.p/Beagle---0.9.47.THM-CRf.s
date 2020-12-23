%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 412 expanded)
%              Number of leaves         :   42 ( 172 expanded)
%              Depth                    :   12
%              Number of atoms          :  417 (3368 expanded)
%              Number of equality atoms :   49 ( 203 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_38,plain,(
    '#skF_6' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_42,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_89,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_90,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_562,plain,(
    ! [A_285,F_281,D_282,C_283,B_284] :
      ( r1_funct_2(A_285,B_284,C_283,D_282,F_281,F_281)
      | ~ m1_subset_1(F_281,k1_zfmisc_1(k2_zfmisc_1(C_283,D_282)))
      | ~ v1_funct_2(F_281,C_283,D_282)
      | ~ m1_subset_1(F_281,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_2(F_281,A_285,B_284)
      | ~ v1_funct_1(F_281)
      | v1_xboole_0(D_282)
      | v1_xboole_0(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_564,plain,(
    ! [A_285,B_284] :
      ( r1_funct_2(A_285,B_284,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_2('#skF_9',A_285,B_284)
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_284) ) ),
    inference(resolution,[status(thm)],[c_90,c_562])).

tff(c_571,plain,(
    ! [A_285,B_284] :
      ( r1_funct_2(A_285,B_284,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_2('#skF_9',A_285,B_284)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_89,c_564])).

tff(c_578,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_213] :
      ( m1_subset_1('#skF_2'(A_213),k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_172,plain,(
    ! [A_218,A_219] :
      ( ~ v1_xboole_0(u1_struct_0(A_218))
      | ~ r2_hidden(A_219,'#skF_2'(A_218))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_157,c_18])).

tff(c_183,plain,(
    ! [A_220,B_221] :
      ( ~ v1_xboole_0(u1_struct_0(A_220))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220)
      | r1_tarski('#skF_2'(A_220),B_221) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_195,A_196] :
      ( B_195 = A_196
      | ~ r1_tarski(B_195,A_196)
      | ~ r1_tarski(A_196,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_99])).

tff(c_190,plain,(
    ! [A_220] :
      ( '#skF_2'(A_220) = k1_xboole_0
      | ~ v1_xboole_0(u1_struct_0(A_220))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_183,c_108])).

tff(c_583,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_578,c_190])).

tff(c_590,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_583])).

tff(c_591,plain,(
    '#skF_2'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_590])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_2'(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_612,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_22])).

tff(c_634,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8,c_612])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_634])).

tff(c_638,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_36,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_91,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_644,plain,(
    ! [F_289,A_293,B_292,D_290,C_291,E_288] :
      ( F_289 = E_288
      | ~ r1_funct_2(A_293,B_292,C_291,D_290,E_288,F_289)
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(C_291,D_290)))
      | ~ v1_funct_2(F_289,C_291,D_290)
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292)))
      | ~ v1_funct_2(E_288,A_293,B_292)
      | ~ v1_funct_1(E_288)
      | v1_xboole_0(D_290)
      | v1_xboole_0(B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_648,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_91,c_644])).

tff(c_656,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_44,c_89,c_90,c_648])).

tff(c_657,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_656])).

tff(c_280,plain,(
    ! [D_242,B_244,A_245,C_243,F_241] :
      ( r1_funct_2(A_245,B_244,C_243,D_242,F_241,F_241)
      | ~ m1_subset_1(F_241,k1_zfmisc_1(k2_zfmisc_1(C_243,D_242)))
      | ~ v1_funct_2(F_241,C_243,D_242)
      | ~ m1_subset_1(F_241,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2(F_241,A_245,B_244)
      | ~ v1_funct_1(F_241)
      | v1_xboole_0(D_242)
      | v1_xboole_0(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_282,plain,(
    ! [A_245,B_244] :
      ( r1_funct_2(A_245,B_244,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2('#skF_9',A_245,B_244)
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_244) ) ),
    inference(resolution,[status(thm)],[c_90,c_280])).

tff(c_289,plain,(
    ! [A_245,B_244] :
      ( r1_funct_2(A_245,B_244,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2('#skF_9',A_245,B_244)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_89,c_282])).

tff(c_296,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_301,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_296,c_190])).

tff(c_308,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_301])).

tff(c_309,plain,(
    '#skF_2'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_308])).

tff(c_330,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_22])).

tff(c_352,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8,c_330])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_352])).

tff(c_356,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_362,plain,(
    ! [B_252,D_250,F_249,E_248,A_253,C_251] :
      ( F_249 = E_248
      | ~ r1_funct_2(A_253,B_252,C_251,D_250,E_248,F_249)
      | ~ m1_subset_1(F_249,k1_zfmisc_1(k2_zfmisc_1(C_251,D_250)))
      | ~ v1_funct_2(F_249,C_251,D_250)
      | ~ v1_funct_1(F_249)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_253,B_252)))
      | ~ v1_funct_2(E_248,A_253,B_252)
      | ~ v1_funct_1(E_248)
      | v1_xboole_0(D_250)
      | v1_xboole_0(B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_366,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_91,c_362])).

tff(c_374,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_44,c_89,c_90,c_366])).

tff(c_375,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_374])).

tff(c_84,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_86,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_216,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_376,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_216])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_87,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58])).

tff(c_428,plain,(
    ! [A_261,E_264,D_262,C_265,B_263] :
      ( k3_tmap_1(A_261,B_263,C_265,D_262,E_264) = k2_partfun1(u1_struct_0(C_265),u1_struct_0(B_263),E_264,u1_struct_0(D_262))
      | ~ m1_pre_topc(D_262,C_265)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_265),u1_struct_0(B_263))))
      | ~ v1_funct_2(E_264,u1_struct_0(C_265),u1_struct_0(B_263))
      | ~ v1_funct_1(E_264)
      | ~ m1_pre_topc(D_262,A_261)
      | ~ m1_pre_topc(C_265,A_261)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_430,plain,(
    ! [A_261,D_262] :
      ( k3_tmap_1(A_261,'#skF_4','#skF_3',D_262,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_262))
      | ~ m1_pre_topc(D_262,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_262,A_261)
      | ~ m1_pre_topc('#skF_3',A_261)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_90,c_428])).

tff(c_435,plain,(
    ! [A_261,D_262] :
      ( k3_tmap_1(A_261,'#skF_4','#skF_3',D_262,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_262))
      | ~ m1_pre_topc(D_262,'#skF_3')
      | ~ m1_pre_topc(D_262,A_261)
      | ~ m1_pre_topc('#skF_3',A_261)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_44,c_89,c_430])).

tff(c_441,plain,(
    ! [A_266,D_267] :
      ( k3_tmap_1(A_266,'#skF_4','#skF_3',D_267,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_267))
      | ~ m1_pre_topc(D_267,'#skF_3')
      | ~ m1_pre_topc(D_267,A_266)
      | ~ m1_pre_topc('#skF_3',A_266)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_435])).

tff(c_445,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_441])).

tff(c_453,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_87,c_62,c_445])).

tff(c_454,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_453])).

tff(c_405,plain,(
    ! [A_256,B_257,C_258,D_259] :
      ( k2_partfun1(u1_struct_0(A_256),u1_struct_0(B_257),C_258,u1_struct_0(D_259)) = k2_tmap_1(A_256,B_257,C_258,D_259)
      | ~ m1_pre_topc(D_259,A_256)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256),u1_struct_0(B_257))))
      | ~ v1_funct_2(C_258,u1_struct_0(A_256),u1_struct_0(B_257))
      | ~ v1_funct_1(C_258)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_407,plain,(
    ! [D_259] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_259)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_259)
      | ~ m1_pre_topc(D_259,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_405])).

tff(c_412,plain,(
    ! [D_259] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_259)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_259)
      | ~ m1_pre_topc(D_259,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_44,c_89,c_407])).

tff(c_413,plain,(
    ! [D_259] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_259)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_259)
      | ~ m1_pre_topc(D_259,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_412])).

tff(c_462,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_413])).

tff(c_469,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_462])).

tff(c_78,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_88,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_78])).

tff(c_233,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_88])).

tff(c_474,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_233])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_474])).

tff(c_479,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_658,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_479])).

tff(c_710,plain,(
    ! [C_305,D_302,A_301,E_304,B_303] :
      ( k3_tmap_1(A_301,B_303,C_305,D_302,E_304) = k2_partfun1(u1_struct_0(C_305),u1_struct_0(B_303),E_304,u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,C_305)
      | ~ m1_subset_1(E_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305),u1_struct_0(B_303))))
      | ~ v1_funct_2(E_304,u1_struct_0(C_305),u1_struct_0(B_303))
      | ~ v1_funct_1(E_304)
      | ~ m1_pre_topc(D_302,A_301)
      | ~ m1_pre_topc(C_305,A_301)
      | ~ l1_pre_topc(B_303)
      | ~ v2_pre_topc(B_303)
      | v2_struct_0(B_303)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_712,plain,(
    ! [A_301,D_302] :
      ( k3_tmap_1(A_301,'#skF_4','#skF_3',D_302,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_302,A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_90,c_710])).

tff(c_717,plain,(
    ! [A_301,D_302] :
      ( k3_tmap_1(A_301,'#skF_4','#skF_3',D_302,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_302))
      | ~ m1_pre_topc(D_302,'#skF_3')
      | ~ m1_pre_topc(D_302,A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_44,c_89,c_712])).

tff(c_723,plain,(
    ! [A_306,D_307] :
      ( k3_tmap_1(A_306,'#skF_4','#skF_3',D_307,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_307))
      | ~ m1_pre_topc(D_307,'#skF_3')
      | ~ m1_pre_topc(D_307,A_306)
      | ~ m1_pre_topc('#skF_3',A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_717])).

tff(c_727,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_723])).

tff(c_735,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_87,c_62,c_727])).

tff(c_736,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_735])).

tff(c_687,plain,(
    ! [A_296,B_297,C_298,D_299] :
      ( k2_partfun1(u1_struct_0(A_296),u1_struct_0(B_297),C_298,u1_struct_0(D_299)) = k2_tmap_1(A_296,B_297,C_298,D_299)
      | ~ m1_pre_topc(D_299,A_296)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_296),u1_struct_0(B_297))))
      | ~ v1_funct_2(C_298,u1_struct_0(A_296),u1_struct_0(B_297))
      | ~ v1_funct_1(C_298)
      | ~ l1_pre_topc(B_297)
      | ~ v2_pre_topc(B_297)
      | v2_struct_0(B_297)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_689,plain,(
    ! [D_299] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_299)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_299)
      | ~ m1_pre_topc(D_299,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_687])).

tff(c_694,plain,(
    ! [D_299] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_299)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_299)
      | ~ m1_pre_topc(D_299,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_44,c_89,c_689])).

tff(c_695,plain,(
    ! [D_299] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_299)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_299)
      | ~ m1_pre_topc(D_299,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_694])).

tff(c_744,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_695])).

tff(c_751,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_744])).

tff(c_478,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_756,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_478])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.48  
% 3.37/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.48  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.37/1.48  
% 3.37/1.48  %Foreground sorts:
% 3.37/1.48  
% 3.37/1.48  
% 3.37/1.48  %Background operators:
% 3.37/1.48  
% 3.37/1.48  
% 3.37/1.48  %Foreground operators:
% 3.37/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.37/1.48  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.37/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.37/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.37/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.37/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.37/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.37/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.37/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.48  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.37/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.37/1.48  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.37/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.37/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.37/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.37/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.48  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.37/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.48  
% 3.37/1.50  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.37/1.50  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.37/1.50  tff(f_85, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.37/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.37/1.50  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.37/1.50  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.37/1.50  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.37/1.50  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.37/1.50  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.37/1.50  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.37/1.50  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.50  tff(c_44, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_38, plain, ('#skF_6'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_42, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_89, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 3.37/1.50  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_90, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.37/1.50  tff(c_562, plain, (![A_285, F_281, D_282, C_283, B_284]: (r1_funct_2(A_285, B_284, C_283, D_282, F_281, F_281) | ~m1_subset_1(F_281, k1_zfmisc_1(k2_zfmisc_1(C_283, D_282))) | ~v1_funct_2(F_281, C_283, D_282) | ~m1_subset_1(F_281, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_2(F_281, A_285, B_284) | ~v1_funct_1(F_281) | v1_xboole_0(D_282) | v1_xboole_0(B_284))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.50  tff(c_564, plain, (![A_285, B_284]: (r1_funct_2(A_285, B_284, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_2('#skF_9', A_285, B_284) | ~v1_funct_1('#skF_9') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_284))), inference(resolution, [status(thm)], [c_90, c_562])).
% 3.37/1.50  tff(c_571, plain, (![A_285, B_284]: (r1_funct_2(A_285, B_284, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_2('#skF_9', A_285, B_284) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_284))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_89, c_564])).
% 3.37/1.50  tff(c_578, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_571])).
% 3.37/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.50  tff(c_157, plain, (![A_213]: (m1_subset_1('#skF_2'(A_213), k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.50  tff(c_18, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.37/1.50  tff(c_172, plain, (![A_218, A_219]: (~v1_xboole_0(u1_struct_0(A_218)) | ~r2_hidden(A_219, '#skF_2'(A_218)) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_157, c_18])).
% 3.37/1.50  tff(c_183, plain, (![A_220, B_221]: (~v1_xboole_0(u1_struct_0(A_220)) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220) | r1_tarski('#skF_2'(A_220), B_221))), inference(resolution, [status(thm)], [c_6, c_172])).
% 3.37/1.50  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.37/1.50  tff(c_99, plain, (![B_195, A_196]: (B_195=A_196 | ~r1_tarski(B_195, A_196) | ~r1_tarski(A_196, B_195))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.50  tff(c_108, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_99])).
% 3.37/1.50  tff(c_190, plain, (![A_220]: ('#skF_2'(A_220)=k1_xboole_0 | ~v1_xboole_0(u1_struct_0(A_220)) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_183, c_108])).
% 3.37/1.50  tff(c_583, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_578, c_190])).
% 3.37/1.50  tff(c_590, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_583])).
% 3.37/1.50  tff(c_591, plain, ('#skF_2'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_590])).
% 3.37/1.50  tff(c_22, plain, (![A_12]: (~v1_xboole_0('#skF_2'(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.50  tff(c_612, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_591, c_22])).
% 3.37/1.50  tff(c_634, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_8, c_612])).
% 3.37/1.50  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_634])).
% 3.37/1.50  tff(c_638, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_571])).
% 3.37/1.50  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_54, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_36, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_91, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 3.37/1.50  tff(c_644, plain, (![F_289, A_293, B_292, D_290, C_291, E_288]: (F_289=E_288 | ~r1_funct_2(A_293, B_292, C_291, D_290, E_288, F_289) | ~m1_subset_1(F_289, k1_zfmisc_1(k2_zfmisc_1(C_291, D_290))) | ~v1_funct_2(F_289, C_291, D_290) | ~v1_funct_1(F_289) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))) | ~v1_funct_2(E_288, A_293, B_292) | ~v1_funct_1(E_288) | v1_xboole_0(D_290) | v1_xboole_0(B_292))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.50  tff(c_648, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_91, c_644])).
% 3.37/1.50  tff(c_656, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_44, c_89, c_90, c_648])).
% 3.37/1.50  tff(c_657, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_638, c_656])).
% 3.37/1.50  tff(c_280, plain, (![D_242, B_244, A_245, C_243, F_241]: (r1_funct_2(A_245, B_244, C_243, D_242, F_241, F_241) | ~m1_subset_1(F_241, k1_zfmisc_1(k2_zfmisc_1(C_243, D_242))) | ~v1_funct_2(F_241, C_243, D_242) | ~m1_subset_1(F_241, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2(F_241, A_245, B_244) | ~v1_funct_1(F_241) | v1_xboole_0(D_242) | v1_xboole_0(B_244))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.50  tff(c_282, plain, (![A_245, B_244]: (r1_funct_2(A_245, B_244, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2('#skF_9', A_245, B_244) | ~v1_funct_1('#skF_9') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_244))), inference(resolution, [status(thm)], [c_90, c_280])).
% 3.37/1.50  tff(c_289, plain, (![A_245, B_244]: (r1_funct_2(A_245, B_244, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2('#skF_9', A_245, B_244) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_89, c_282])).
% 3.37/1.50  tff(c_296, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_289])).
% 3.37/1.50  tff(c_301, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_296, c_190])).
% 3.37/1.50  tff(c_308, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_301])).
% 3.37/1.50  tff(c_309, plain, ('#skF_2'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_308])).
% 3.37/1.50  tff(c_330, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_309, c_22])).
% 3.37/1.50  tff(c_352, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_8, c_330])).
% 3.37/1.50  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_352])).
% 3.37/1.50  tff(c_356, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_289])).
% 3.37/1.50  tff(c_362, plain, (![B_252, D_250, F_249, E_248, A_253, C_251]: (F_249=E_248 | ~r1_funct_2(A_253, B_252, C_251, D_250, E_248, F_249) | ~m1_subset_1(F_249, k1_zfmisc_1(k2_zfmisc_1(C_251, D_250))) | ~v1_funct_2(F_249, C_251, D_250) | ~v1_funct_1(F_249) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_253, B_252))) | ~v1_funct_2(E_248, A_253, B_252) | ~v1_funct_1(E_248) | v1_xboole_0(D_250) | v1_xboole_0(B_252))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.50  tff(c_366, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_91, c_362])).
% 3.37/1.50  tff(c_374, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_44, c_89, c_90, c_366])).
% 3.37/1.50  tff(c_375, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_356, c_374])).
% 3.37/1.50  tff(c_84, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_86, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_84])).
% 3.37/1.50  tff(c_216, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 3.37/1.50  tff(c_376, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_216])).
% 3.37/1.50  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_58, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_87, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58])).
% 3.37/1.50  tff(c_428, plain, (![A_261, E_264, D_262, C_265, B_263]: (k3_tmap_1(A_261, B_263, C_265, D_262, E_264)=k2_partfun1(u1_struct_0(C_265), u1_struct_0(B_263), E_264, u1_struct_0(D_262)) | ~m1_pre_topc(D_262, C_265) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_265), u1_struct_0(B_263)))) | ~v1_funct_2(E_264, u1_struct_0(C_265), u1_struct_0(B_263)) | ~v1_funct_1(E_264) | ~m1_pre_topc(D_262, A_261) | ~m1_pre_topc(C_265, A_261) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.37/1.50  tff(c_430, plain, (![A_261, D_262]: (k3_tmap_1(A_261, '#skF_4', '#skF_3', D_262, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_262)) | ~m1_pre_topc(D_262, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_262, A_261) | ~m1_pre_topc('#skF_3', A_261) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_90, c_428])).
% 3.37/1.50  tff(c_435, plain, (![A_261, D_262]: (k3_tmap_1(A_261, '#skF_4', '#skF_3', D_262, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_262)) | ~m1_pre_topc(D_262, '#skF_3') | ~m1_pre_topc(D_262, A_261) | ~m1_pre_topc('#skF_3', A_261) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_44, c_89, c_430])).
% 3.37/1.50  tff(c_441, plain, (![A_266, D_267]: (k3_tmap_1(A_266, '#skF_4', '#skF_3', D_267, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_267)) | ~m1_pre_topc(D_267, '#skF_3') | ~m1_pre_topc(D_267, A_266) | ~m1_pre_topc('#skF_3', A_266) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(negUnitSimplification, [status(thm)], [c_70, c_435])).
% 3.37/1.50  tff(c_445, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_441])).
% 3.37/1.50  tff(c_453, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_87, c_62, c_445])).
% 3.37/1.50  tff(c_454, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_76, c_453])).
% 3.37/1.50  tff(c_405, plain, (![A_256, B_257, C_258, D_259]: (k2_partfun1(u1_struct_0(A_256), u1_struct_0(B_257), C_258, u1_struct_0(D_259))=k2_tmap_1(A_256, B_257, C_258, D_259) | ~m1_pre_topc(D_259, A_256) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256), u1_struct_0(B_257)))) | ~v1_funct_2(C_258, u1_struct_0(A_256), u1_struct_0(B_257)) | ~v1_funct_1(C_258) | ~l1_pre_topc(B_257) | ~v2_pre_topc(B_257) | v2_struct_0(B_257) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.37/1.50  tff(c_407, plain, (![D_259]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_259))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_259) | ~m1_pre_topc(D_259, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_405])).
% 3.37/1.50  tff(c_412, plain, (![D_259]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_259))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_259) | ~m1_pre_topc(D_259, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_44, c_89, c_407])).
% 3.37/1.50  tff(c_413, plain, (![D_259]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_259))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_259) | ~m1_pre_topc(D_259, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_412])).
% 3.37/1.50  tff(c_462, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_454, c_413])).
% 3.37/1.50  tff(c_469, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_462])).
% 3.37/1.50  tff(c_78, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.37/1.50  tff(c_88, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_78])).
% 3.37/1.50  tff(c_233, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_88])).
% 3.37/1.50  tff(c_474, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_233])).
% 3.37/1.50  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_474])).
% 3.37/1.50  tff(c_479, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 3.37/1.50  tff(c_658, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_657, c_479])).
% 3.37/1.50  tff(c_710, plain, (![C_305, D_302, A_301, E_304, B_303]: (k3_tmap_1(A_301, B_303, C_305, D_302, E_304)=k2_partfun1(u1_struct_0(C_305), u1_struct_0(B_303), E_304, u1_struct_0(D_302)) | ~m1_pre_topc(D_302, C_305) | ~m1_subset_1(E_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305), u1_struct_0(B_303)))) | ~v1_funct_2(E_304, u1_struct_0(C_305), u1_struct_0(B_303)) | ~v1_funct_1(E_304) | ~m1_pre_topc(D_302, A_301) | ~m1_pre_topc(C_305, A_301) | ~l1_pre_topc(B_303) | ~v2_pre_topc(B_303) | v2_struct_0(B_303) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.37/1.50  tff(c_712, plain, (![A_301, D_302]: (k3_tmap_1(A_301, '#skF_4', '#skF_3', D_302, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_302)) | ~m1_pre_topc(D_302, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_302, A_301) | ~m1_pre_topc('#skF_3', A_301) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(resolution, [status(thm)], [c_90, c_710])).
% 3.37/1.50  tff(c_717, plain, (![A_301, D_302]: (k3_tmap_1(A_301, '#skF_4', '#skF_3', D_302, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_302)) | ~m1_pre_topc(D_302, '#skF_3') | ~m1_pre_topc(D_302, A_301) | ~m1_pre_topc('#skF_3', A_301) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_44, c_89, c_712])).
% 3.37/1.50  tff(c_723, plain, (![A_306, D_307]: (k3_tmap_1(A_306, '#skF_4', '#skF_3', D_307, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_307)) | ~m1_pre_topc(D_307, '#skF_3') | ~m1_pre_topc(D_307, A_306) | ~m1_pre_topc('#skF_3', A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(negUnitSimplification, [status(thm)], [c_70, c_717])).
% 3.37/1.50  tff(c_727, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_723])).
% 3.37/1.50  tff(c_735, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_87, c_62, c_727])).
% 3.37/1.50  tff(c_736, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_76, c_735])).
% 3.37/1.50  tff(c_687, plain, (![A_296, B_297, C_298, D_299]: (k2_partfun1(u1_struct_0(A_296), u1_struct_0(B_297), C_298, u1_struct_0(D_299))=k2_tmap_1(A_296, B_297, C_298, D_299) | ~m1_pre_topc(D_299, A_296) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_296), u1_struct_0(B_297)))) | ~v1_funct_2(C_298, u1_struct_0(A_296), u1_struct_0(B_297)) | ~v1_funct_1(C_298) | ~l1_pre_topc(B_297) | ~v2_pre_topc(B_297) | v2_struct_0(B_297) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.37/1.50  tff(c_689, plain, (![D_299]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_299))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_299) | ~m1_pre_topc(D_299, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_687])).
% 3.37/1.50  tff(c_694, plain, (![D_299]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_299))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_299) | ~m1_pre_topc(D_299, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_44, c_89, c_689])).
% 3.37/1.50  tff(c_695, plain, (![D_299]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_299))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_299) | ~m1_pre_topc(D_299, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_694])).
% 3.37/1.50  tff(c_744, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_736, c_695])).
% 3.37/1.50  tff(c_751, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_744])).
% 3.37/1.50  tff(c_478, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 3.37/1.50  tff(c_756, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_478])).
% 3.37/1.50  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_756])).
% 3.37/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.50  
% 3.37/1.50  Inference rules
% 3.37/1.50  ----------------------
% 3.37/1.50  #Ref     : 0
% 3.37/1.50  #Sup     : 120
% 3.37/1.50  #Fact    : 0
% 3.37/1.50  #Define  : 0
% 3.37/1.50  #Split   : 10
% 3.37/1.50  #Chain   : 0
% 3.37/1.50  #Close   : 0
% 3.37/1.50  
% 3.37/1.50  Ordering : KBO
% 3.37/1.50  
% 3.37/1.50  Simplification rules
% 3.37/1.50  ----------------------
% 3.37/1.50  #Subsume      : 31
% 3.37/1.50  #Demod        : 212
% 3.37/1.50  #Tautology    : 54
% 3.37/1.50  #SimpNegUnit  : 43
% 3.37/1.50  #BackRed      : 14
% 3.37/1.50  
% 3.37/1.50  #Partial instantiations: 0
% 3.37/1.50  #Strategies tried      : 1
% 3.37/1.50  
% 3.37/1.50  Timing (in seconds)
% 3.37/1.50  ----------------------
% 3.37/1.51  Preprocessing        : 0.37
% 3.37/1.51  Parsing              : 0.19
% 3.37/1.51  CNF conversion       : 0.05
% 3.37/1.51  Main loop            : 0.35
% 3.37/1.51  Inferencing          : 0.12
% 3.37/1.51  Reduction            : 0.12
% 3.37/1.51  Demodulation         : 0.09
% 3.37/1.51  BG Simplification    : 0.02
% 3.37/1.51  Subsumption          : 0.06
% 3.37/1.51  Abstraction          : 0.02
% 3.37/1.51  MUC search           : 0.00
% 3.37/1.51  Cooper               : 0.00
% 3.37/1.51  Total                : 0.77
% 3.37/1.51  Index Insertion      : 0.00
% 3.37/1.51  Index Deletion       : 0.00
% 3.37/1.51  Index Matching       : 0.00
% 3.37/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
