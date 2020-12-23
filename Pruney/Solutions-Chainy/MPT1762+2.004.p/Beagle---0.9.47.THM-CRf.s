%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 910 expanded)
%              Number of leaves         :   36 ( 343 expanded)
%              Depth                    :   18
%              Number of atoms          :  406 (8589 expanded)
%              Number of equality atoms :   44 ( 607 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
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
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_30,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_28,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_81,plain,(
    ! [A_233,B_234,D_235] :
      ( r2_funct_2(A_233,B_234,D_235,D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_2(D_235,A_233,B_234)
      | ~ v1_funct_1(D_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_91,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_85])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    ! [B_228,A_229] :
      ( l1_pre_topc(B_228)
      | ~ m1_pre_topc(B_228,A_229)
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_75,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_12,plain,(
    ! [A_67] :
      ( l1_struct_0(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_36,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_114,plain,(
    ! [E_245,B_244,C_242,A_243,D_241] :
      ( m1_subset_1('#skF_1'(D_241,C_242,A_243,B_244,E_245),A_243)
      | k2_partfun1(A_243,B_244,C_242,D_241) = E_245
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(D_241,B_244)))
      | ~ v1_funct_2(E_245,D_241,B_244)
      | ~ v1_funct_1(E_245)
      | ~ m1_subset_1(D_241,k1_zfmisc_1(A_243))
      | v1_xboole_0(D_241)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_2(C_242,A_243,B_244)
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(B_244)
      | v1_xboole_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_116,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_6'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_243))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_121,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_6'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_243))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_116])).

tff(c_125,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_16,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(u1_struct_0(A_71))
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_128,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_131,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_128])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134])).

tff(c_139,plain,(
    ! [C_242,A_243] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_6'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_243))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(A_243) ) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_154,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_157,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_16])).

tff(c_160,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_157])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_163])).

tff(c_169,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_20,plain,(
    ! [B_105,A_103] :
      ( m1_subset_1(u1_struct_0(B_105),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_pre_topc(B_105,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_63])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_140,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_118,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_7'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_243))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_124,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_7'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_243))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_118])).

tff(c_170,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_7'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_243))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_124])).

tff(c_171,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_174,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_16])).

tff(c_177,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_174])).

tff(c_180,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_180])).

tff(c_186,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_187,plain,(
    ! [E_252,C_253,D_255,B_254,A_251] :
      ( k3_tmap_1(A_251,B_254,C_253,D_255,E_252) = k2_partfun1(u1_struct_0(C_253),u1_struct_0(B_254),E_252,u1_struct_0(D_255))
      | ~ m1_pre_topc(D_255,C_253)
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_253),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_252,u1_struct_0(C_253),u1_struct_0(B_254))
      | ~ v1_funct_1(E_252)
      | ~ m1_pre_topc(D_255,A_251)
      | ~ m1_pre_topc(C_253,A_251)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_189,plain,(
    ! [A_251,D_255] :
      ( k3_tmap_1(A_251,'#skF_3','#skF_5',D_255,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_255))
      | ~ m1_pre_topc(D_255,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_255,A_251)
      | ~ m1_pre_topc('#skF_5',A_251)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_194,plain,(
    ! [A_251,D_255] :
      ( k3_tmap_1(A_251,'#skF_3','#skF_5',D_255,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_255))
      | ~ m1_pre_topc(D_255,'#skF_5')
      | ~ m1_pre_topc(D_255,A_251)
      | ~ m1_pre_topc('#skF_5',A_251)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_189])).

tff(c_200,plain,(
    ! [A_256,D_257] :
      ( k3_tmap_1(A_256,'#skF_3','#skF_5',D_257,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_257))
      | ~ m1_pre_topc(D_257,'#skF_5')
      | ~ m1_pre_topc(D_257,A_256)
      | ~ m1_pre_topc('#skF_5',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_194])).

tff(c_202,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_200])).

tff(c_209,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_32,c_202])).

tff(c_210,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_209])).

tff(c_141,plain,(
    ! [B_249,C_247,A_248,E_250,D_246] :
      ( r2_hidden('#skF_1'(D_246,C_247,A_248,B_249,E_250),D_246)
      | k2_partfun1(A_248,B_249,C_247,D_246) = E_250
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(D_246,B_249)))
      | ~ v1_funct_2(E_250,D_246,B_249)
      | ~ v1_funct_1(E_250)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(A_248))
      | v1_xboole_0(D_246)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_2(C_247,A_248,B_249)
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(B_249)
      | v1_xboole_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_145,plain,(
    ! [C_247,A_248] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_247,A_248,u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_248,u1_struct_0('#skF_3'),C_247,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_248))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_247,A_248,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_152,plain,(
    ! [C_247,A_248] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_247,A_248,u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_248,u1_struct_0('#skF_3'),C_247,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_248))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_247,A_248,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_145])).

tff(c_153,plain,(
    ! [C_247,A_248] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_247,A_248,u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_248,u1_struct_0('#skF_3'),C_247,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_248))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_247,A_248,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(A_248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_152])).

tff(c_271,plain,(
    ! [C_247,A_248] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_247,A_248,u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_248,u1_struct_0('#skF_3'),C_247,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_248))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_247,A_248,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(A_248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_153])).

tff(c_24,plain,(
    ! [G_226] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',G_226) = k1_funct_1('#skF_7',G_226)
      | ~ r2_hidden(G_226,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_226,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_246,plain,(
    ! [D_260,E_264,C_261,A_262,B_263] :
      ( k3_funct_2(A_262,B_263,C_261,'#skF_1'(D_260,C_261,A_262,B_263,E_264)) != k1_funct_1(E_264,'#skF_1'(D_260,C_261,A_262,B_263,E_264))
      | k2_partfun1(A_262,B_263,C_261,D_260) = E_264
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(D_260,B_263)))
      | ~ v1_funct_2(E_264,D_260,B_263)
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(A_262))
      | v1_xboole_0(D_260)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_2(C_261,A_262,B_263)
      | ~ v1_funct_1(C_261)
      | v1_xboole_0(B_263)
      | v1_xboole_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_249,plain,(
    ! [E_264,D_260] :
      ( k1_funct_1(E_264,'#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264)) != k1_funct_1('#skF_7','#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_260) = E_264
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(D_260,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_264,D_260,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_260)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_246])).

tff(c_251,plain,(
    ! [E_264,D_260] :
      ( k1_funct_1(E_264,'#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264)) != k1_funct_1('#skF_7','#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_260) = E_264
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(D_260,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_264,D_260,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_260)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_249])).

tff(c_252,plain,(
    ! [E_264,D_260] :
      ( k1_funct_1(E_264,'#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264)) != k1_funct_1('#skF_7','#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_260) = E_264
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(D_260,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_264,D_260,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_260)
      | ~ r2_hidden('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),E_264),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_140,c_251])).

tff(c_294,plain,(
    ! [D_260] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_260) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_260,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_260,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_260,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_260)
      | ~ r2_hidden('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_260,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_252])).

tff(c_298,plain,(
    ! [D_275] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_275) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_275,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_275,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_275,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_275)
      | ~ r2_hidden('#skF_1'(D_275,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_275,'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_302,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_271,c_298])).

tff(c_305,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_210,c_28,c_26,c_302])).

tff(c_306,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_186,c_305])).

tff(c_307,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_315,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_307])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_32,c_315])).

tff(c_321,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_185,plain,(
    ! [C_242,A_243] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_242,A_243,u1_struct_0('#skF_3'),'#skF_7'),A_243)
      | k2_partfun1(A_243,u1_struct_0('#skF_3'),C_242,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_243))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_242,A_243,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_242)
      | v1_xboole_0(A_243) ) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_320,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_322,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_330,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_185,c_322])).

tff(c_333,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_321,c_210,c_330])).

tff(c_334,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_333])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_336,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_22])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_336])).

tff(c_340,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_343,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_22])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.47  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.26/1.47  
% 3.26/1.47  %Foreground sorts:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Background operators:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Foreground operators:
% 3.26/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.26/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.26/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.26/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.26/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.26/1.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.26/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.26/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.47  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.26/1.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.26/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.47  
% 3.26/1.50  tff(f_188, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((![G]: (m1_subset_1(G, u1_struct_0(D)) => (r2_hidden(G, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, G) = k1_funct_1(F, G))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 3.26/1.50  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.26/1.50  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.26/1.50  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.26/1.50  tff(f_77, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, D, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((![F]: (m1_subset_1(F, A) => (r2_hidden(F, D) => (k3_funct_2(A, B, C, F) = k1_funct_1(E, F))))) => (k2_partfun1(A, B, C, D) = E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 3.26/1.50  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.26/1.50  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.26/1.50  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.26/1.50  tff(c_30, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_28, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_26, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_81, plain, (![A_233, B_234, D_235]: (r2_funct_2(A_233, B_234, D_235, D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_2(D_235, A_233, B_234) | ~v1_funct_1(D_235))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.50  tff(c_85, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_81])).
% 3.26/1.50  tff(c_91, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_85])).
% 3.26/1.50  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_60, plain, (![B_228, A_229]: (l1_pre_topc(B_228) | ~m1_pre_topc(B_228, A_229) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.50  tff(c_66, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.26/1.50  tff(c_75, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66])).
% 3.26/1.50  tff(c_12, plain, (![A_67]: (l1_struct_0(A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.26/1.50  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_36, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_114, plain, (![E_245, B_244, C_242, A_243, D_241]: (m1_subset_1('#skF_1'(D_241, C_242, A_243, B_244, E_245), A_243) | k2_partfun1(A_243, B_244, C_242, D_241)=E_245 | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(D_241, B_244))) | ~v1_funct_2(E_245, D_241, B_244) | ~v1_funct_1(E_245) | ~m1_subset_1(D_241, k1_zfmisc_1(A_243)) | v1_xboole_0(D_241) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_2(C_242, A_243, B_244) | ~v1_funct_1(C_242) | v1_xboole_0(B_244) | v1_xboole_0(A_243))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.50  tff(c_116, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_6'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_5'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_243)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_34, c_114])).
% 3.26/1.50  tff(c_121, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_6'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_243)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_116])).
% 3.26/1.50  tff(c_125, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_121])).
% 3.26/1.50  tff(c_16, plain, (![A_71]: (~v1_xboole_0(u1_struct_0(A_71)) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.26/1.50  tff(c_128, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_16])).
% 3.26/1.50  tff(c_131, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_128])).
% 3.26/1.50  tff(c_134, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_131])).
% 3.26/1.50  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_134])).
% 3.26/1.50  tff(c_139, plain, (![C_242, A_243]: (v1_xboole_0(u1_struct_0('#skF_5')) | m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_6'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_243)) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(A_243))), inference(splitRight, [status(thm)], [c_121])).
% 3.26/1.50  tff(c_154, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_139])).
% 3.26/1.50  tff(c_157, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_154, c_16])).
% 3.26/1.50  tff(c_160, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_157])).
% 3.26/1.50  tff(c_163, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_160])).
% 3.26/1.50  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_163])).
% 3.26/1.50  tff(c_169, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_139])).
% 3.26/1.50  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_20, plain, (![B_105, A_103]: (m1_subset_1(u1_struct_0(B_105), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_pre_topc(B_105, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_63, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_60])).
% 3.26/1.50  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_63])).
% 3.26/1.50  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_140, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_121])).
% 3.26/1.50  tff(c_118, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_7'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_4'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_243)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_26, c_114])).
% 3.26/1.50  tff(c_124, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_7'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_243)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_118])).
% 3.26/1.50  tff(c_170, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_7'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_243)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(A_243))), inference(negUnitSimplification, [status(thm)], [c_140, c_124])).
% 3.26/1.50  tff(c_171, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_170])).
% 3.26/1.50  tff(c_174, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_171, c_16])).
% 3.26/1.50  tff(c_177, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_174])).
% 3.26/1.50  tff(c_180, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_177])).
% 3.26/1.50  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_180])).
% 3.26/1.50  tff(c_186, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_170])).
% 3.26/1.50  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_187, plain, (![E_252, C_253, D_255, B_254, A_251]: (k3_tmap_1(A_251, B_254, C_253, D_255, E_252)=k2_partfun1(u1_struct_0(C_253), u1_struct_0(B_254), E_252, u1_struct_0(D_255)) | ~m1_pre_topc(D_255, C_253) | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_253), u1_struct_0(B_254)))) | ~v1_funct_2(E_252, u1_struct_0(C_253), u1_struct_0(B_254)) | ~v1_funct_1(E_252) | ~m1_pre_topc(D_255, A_251) | ~m1_pre_topc(C_253, A_251) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.50  tff(c_189, plain, (![A_251, D_255]: (k3_tmap_1(A_251, '#skF_3', '#skF_5', D_255, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_255)) | ~m1_pre_topc(D_255, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_255, A_251) | ~m1_pre_topc('#skF_5', A_251) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_34, c_187])).
% 3.26/1.50  tff(c_194, plain, (![A_251, D_255]: (k3_tmap_1(A_251, '#skF_3', '#skF_5', D_255, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_255)) | ~m1_pre_topc(D_255, '#skF_5') | ~m1_pre_topc(D_255, A_251) | ~m1_pre_topc('#skF_5', A_251) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_189])).
% 3.26/1.50  tff(c_200, plain, (![A_256, D_257]: (k3_tmap_1(A_256, '#skF_3', '#skF_5', D_257, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_257)) | ~m1_pre_topc(D_257, '#skF_5') | ~m1_pre_topc(D_257, A_256) | ~m1_pre_topc('#skF_5', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(negUnitSimplification, [status(thm)], [c_52, c_194])).
% 3.26/1.50  tff(c_202, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_200])).
% 3.26/1.50  tff(c_209, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_32, c_202])).
% 3.26/1.50  tff(c_210, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_209])).
% 3.26/1.50  tff(c_141, plain, (![B_249, C_247, A_248, E_250, D_246]: (r2_hidden('#skF_1'(D_246, C_247, A_248, B_249, E_250), D_246) | k2_partfun1(A_248, B_249, C_247, D_246)=E_250 | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(D_246, B_249))) | ~v1_funct_2(E_250, D_246, B_249) | ~v1_funct_1(E_250) | ~m1_subset_1(D_246, k1_zfmisc_1(A_248)) | v1_xboole_0(D_246) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_2(C_247, A_248, B_249) | ~v1_funct_1(C_247) | v1_xboole_0(B_249) | v1_xboole_0(A_248))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.50  tff(c_145, plain, (![C_247, A_248]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_247, A_248, u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | k2_partfun1(A_248, u1_struct_0('#skF_3'), C_247, u1_struct_0('#skF_4'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_248)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_247, A_248, u1_struct_0('#skF_3')) | ~v1_funct_1(C_247) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_248))), inference(resolution, [status(thm)], [c_26, c_141])).
% 3.26/1.50  tff(c_152, plain, (![C_247, A_248]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_247, A_248, u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | k2_partfun1(A_248, u1_struct_0('#skF_3'), C_247, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_248)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_247, A_248, u1_struct_0('#skF_3')) | ~v1_funct_1(C_247) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_145])).
% 3.26/1.50  tff(c_153, plain, (![C_247, A_248]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_247, A_248, u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | k2_partfun1(A_248, u1_struct_0('#skF_3'), C_247, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_248)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_247, A_248, u1_struct_0('#skF_3')) | ~v1_funct_1(C_247) | v1_xboole_0(A_248))), inference(negUnitSimplification, [status(thm)], [c_140, c_152])).
% 3.26/1.50  tff(c_271, plain, (![C_247, A_248]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_247, A_248, u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | k2_partfun1(A_248, u1_struct_0('#skF_3'), C_247, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_248)) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_247, A_248, u1_struct_0('#skF_3')) | ~v1_funct_1(C_247) | v1_xboole_0(A_248))), inference(negUnitSimplification, [status(thm)], [c_186, c_153])).
% 3.26/1.50  tff(c_24, plain, (![G_226]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', G_226)=k1_funct_1('#skF_7', G_226) | ~r2_hidden(G_226, u1_struct_0('#skF_4')) | ~m1_subset_1(G_226, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_246, plain, (![D_260, E_264, C_261, A_262, B_263]: (k3_funct_2(A_262, B_263, C_261, '#skF_1'(D_260, C_261, A_262, B_263, E_264))!=k1_funct_1(E_264, '#skF_1'(D_260, C_261, A_262, B_263, E_264)) | k2_partfun1(A_262, B_263, C_261, D_260)=E_264 | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(D_260, B_263))) | ~v1_funct_2(E_264, D_260, B_263) | ~v1_funct_1(E_264) | ~m1_subset_1(D_260, k1_zfmisc_1(A_262)) | v1_xboole_0(D_260) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_2(C_261, A_262, B_263) | ~v1_funct_1(C_261) | v1_xboole_0(B_263) | v1_xboole_0(A_262))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.50  tff(c_249, plain, (![E_264, D_260]: (k1_funct_1(E_264, '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264))!=k1_funct_1('#skF_7', '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_260)=E_264 | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(D_260, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_264, D_260, u1_struct_0('#skF_3')) | ~v1_funct_1(E_264) | ~m1_subset_1(D_260, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_260) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_246])).
% 3.26/1.50  tff(c_251, plain, (![E_264, D_260]: (k1_funct_1(E_264, '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264))!=k1_funct_1('#skF_7', '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_260)=E_264 | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(D_260, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_264, D_260, u1_struct_0('#skF_3')) | ~v1_funct_1(E_264) | ~m1_subset_1(D_260, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_260) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_249])).
% 3.26/1.50  tff(c_252, plain, (![E_264, D_260]: (k1_funct_1(E_264, '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264))!=k1_funct_1('#skF_7', '#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_260)=E_264 | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(D_260, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_264, D_260, u1_struct_0('#skF_3')) | ~v1_funct_1(E_264) | ~m1_subset_1(D_260, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_260) | ~r2_hidden('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), E_264), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_169, c_140, c_251])).
% 3.26/1.50  tff(c_294, plain, (![D_260]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_260)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_260, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_260, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_260, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_260) | ~r2_hidden('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_260, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')))), inference(reflexivity, [status(thm), theory('equality')], [c_252])).
% 3.26/1.50  tff(c_298, plain, (![D_275]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_275)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_275, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_275, u1_struct_0('#skF_3')) | ~m1_subset_1(D_275, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_275) | ~r2_hidden('#skF_1'(D_275, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_275, '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_294])).
% 3.26/1.50  tff(c_302, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_271, c_298])).
% 3.26/1.50  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_210, c_28, c_26, c_302])).
% 3.26/1.50  tff(c_306, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_169, c_186, c_305])).
% 3.26/1.50  tff(c_307, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_306])).
% 3.26/1.50  tff(c_315, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_307])).
% 3.26/1.50  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_32, c_315])).
% 3.26/1.50  tff(c_321, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_306])).
% 3.26/1.50  tff(c_185, plain, (![C_242, A_243]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_242, A_243, u1_struct_0('#skF_3'), '#skF_7'), A_243) | k2_partfun1(A_243, u1_struct_0('#skF_3'), C_242, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_243)) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_242, A_243, u1_struct_0('#skF_3')) | ~v1_funct_1(C_242) | v1_xboole_0(A_243))), inference(splitRight, [status(thm)], [c_170])).
% 3.26/1.50  tff(c_320, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_306])).
% 3.26/1.50  tff(c_322, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_320])).
% 3.26/1.50  tff(c_330, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_185, c_322])).
% 3.26/1.50  tff(c_333, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_321, c_210, c_330])).
% 3.26/1.50  tff(c_334, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_169, c_333])).
% 3.26/1.50  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.26/1.50  tff(c_336, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_22])).
% 3.26/1.50  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_336])).
% 3.26/1.50  tff(c_340, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_320])).
% 3.26/1.50  tff(c_343, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_22])).
% 3.26/1.50  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_343])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 1
% 3.26/1.50  #Sup     : 43
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 9
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 1
% 3.26/1.50  #Demod        : 74
% 3.26/1.50  #Tautology    : 9
% 3.26/1.50  #SimpNegUnit  : 19
% 3.26/1.50  #BackRed      : 4
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.38
% 3.26/1.50  Parsing              : 0.20
% 3.26/1.50  CNF conversion       : 0.05
% 3.26/1.50  Main loop            : 0.33
% 3.26/1.50  Inferencing          : 0.12
% 3.26/1.50  Reduction            : 0.11
% 3.26/1.50  Demodulation         : 0.08
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.07
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.77
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
