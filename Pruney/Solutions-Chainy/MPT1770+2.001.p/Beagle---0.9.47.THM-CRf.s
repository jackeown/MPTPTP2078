%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 156 expanded)
%              Number of leaves         :   30 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 (1114 expanded)
%              Number of equality atoms :   18 (  63 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_189,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_16,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_18,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_20,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_49,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_14,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_74,plain,(
    ! [B_238,A_239] :
      ( v2_pre_topc(B_238)
      | ~ m1_pre_topc(B_238,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_86,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_77])).

tff(c_55,plain,(
    ! [B_236,A_237] :
      ( l1_pre_topc(B_236)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_67,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_26,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_158,plain,(
    ! [A_252,C_255,D_256,F_253,B_254] :
      ( r1_tmap_1(D_256,A_252,k2_tmap_1(B_254,A_252,C_255,D_256),F_253)
      | ~ r1_tmap_1(B_254,A_252,C_255,F_253)
      | ~ m1_subset_1(F_253,u1_struct_0(D_256))
      | ~ m1_subset_1(F_253,u1_struct_0(B_254))
      | ~ m1_pre_topc(D_256,B_254)
      | v2_struct_0(D_256)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_254),u1_struct_0(A_252))))
      | ~ v1_funct_2(C_255,u1_struct_0(B_254),u1_struct_0(A_252))
      | ~ v1_funct_1(C_255)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_160,plain,(
    ! [D_256,F_253] :
      ( r1_tmap_1(D_256,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_5',D_256),F_253)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_5',F_253)
      | ~ m1_subset_1(F_253,u1_struct_0(D_256))
      | ~ m1_subset_1(F_253,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_256,'#skF_3')
      | v2_struct_0(D_256)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_158])).

tff(c_163,plain,(
    ! [D_256,F_253] :
      ( r1_tmap_1(D_256,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_5',D_256),F_253)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_5',F_253)
      | ~ m1_subset_1(F_253,u1_struct_0(D_256))
      | ~ m1_subset_1(F_253,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_256,'#skF_3')
      | v2_struct_0(D_256)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_86,c_67,c_28,c_26,c_160])).

tff(c_183,plain,(
    ! [D_257,F_258] :
      ( r1_tmap_1(D_257,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_5',D_257),F_258)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_5',F_258)
      | ~ m1_subset_1(F_258,u1_struct_0(D_257))
      | ~ m1_subset_1(F_258,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_257,'#skF_3')
      | v2_struct_0(D_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_163])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_111,plain,(
    ! [C_249,A_246,D_245,B_247,E_248] :
      ( k3_tmap_1(A_246,B_247,C_249,D_245,E_248) = k2_partfun1(u1_struct_0(C_249),u1_struct_0(B_247),E_248,u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,C_249)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249),u1_struct_0(B_247))))
      | ~ v1_funct_2(E_248,u1_struct_0(C_249),u1_struct_0(B_247))
      | ~ v1_funct_1(E_248)
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc(C_249,A_246)
      | ~ l1_pre_topc(B_247)
      | ~ v2_pre_topc(B_247)
      | v2_struct_0(B_247)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_113,plain,(
    ! [A_246,D_245] :
      ( k3_tmap_1(A_246,'#skF_2','#skF_3',D_245,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc('#skF_3',A_246)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_116,plain,(
    ! [A_246,D_245] :
      ( k3_tmap_1(A_246,'#skF_2','#skF_3',D_245,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_245))
      | ~ m1_pre_topc(D_245,'#skF_3')
      | ~ m1_pre_topc(D_245,A_246)
      | ~ m1_pre_topc('#skF_3',A_246)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_26,c_113])).

tff(c_118,plain,(
    ! [A_250,D_251] :
      ( k3_tmap_1(A_250,'#skF_2','#skF_3',D_251,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_251))
      | ~ m1_pre_topc(D_251,'#skF_3')
      | ~ m1_pre_topc(D_251,A_250)
      | ~ m1_pre_topc('#skF_3',A_250)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_116])).

tff(c_122,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_131,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_16,c_122])).

tff(c_132,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_131])).

tff(c_95,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( k2_partfun1(u1_struct_0(A_240),u1_struct_0(B_241),C_242,u1_struct_0(D_243)) = k2_tmap_1(A_240,B_241,C_242,D_243)
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0(B_241))))
      | ~ v1_funct_2(C_242,u1_struct_0(A_240),u1_struct_0(B_241))
      | ~ v1_funct_1(C_242)
      | ~ l1_pre_topc(B_241)
      | ~ v2_pre_topc(B_241)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_97,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_100,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_67,c_40,c_38,c_28,c_26,c_97])).

tff(c_101,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_42,c_100])).

tff(c_140,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_101])).

tff(c_147,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_140])).

tff(c_12,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12])).

tff(c_152,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_50])).

tff(c_186,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_183,c_152])).

tff(c_189,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22,c_49,c_14,c_186])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:35:12 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  %$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.37  
% 2.51/1.37  %Foreground sorts:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Background operators:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Foreground operators:
% 2.51/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.37  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.51/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.51/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.51/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.51/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.51/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.51/1.37  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.51/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.37  
% 2.69/1.38  tff(f_189, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 2.69/1.38  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.69/1.38  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.69/1.38  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 2.69/1.38  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.69/1.38  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.69/1.38  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_16, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_22, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_18, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_20, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_49, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.69/1.38  tff(c_14, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_74, plain, (![B_238, A_239]: (v2_pre_topc(B_238) | ~m1_pre_topc(B_238, A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.38  tff(c_77, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_74])).
% 2.69/1.38  tff(c_86, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_77])).
% 2.69/1.38  tff(c_55, plain, (![B_236, A_237]: (l1_pre_topc(B_236) | ~m1_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.38  tff(c_58, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.69/1.38  tff(c_67, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 2.69/1.38  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_26, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.38  tff(c_158, plain, (![A_252, C_255, D_256, F_253, B_254]: (r1_tmap_1(D_256, A_252, k2_tmap_1(B_254, A_252, C_255, D_256), F_253) | ~r1_tmap_1(B_254, A_252, C_255, F_253) | ~m1_subset_1(F_253, u1_struct_0(D_256)) | ~m1_subset_1(F_253, u1_struct_0(B_254)) | ~m1_pre_topc(D_256, B_254) | v2_struct_0(D_256) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_254), u1_struct_0(A_252)))) | ~v1_funct_2(C_255, u1_struct_0(B_254), u1_struct_0(A_252)) | ~v1_funct_1(C_255) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.69/1.38  tff(c_160, plain, (![D_256, F_253]: (r1_tmap_1(D_256, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_256), F_253) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_5', F_253) | ~m1_subset_1(F_253, u1_struct_0(D_256)) | ~m1_subset_1(F_253, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_256, '#skF_3') | v2_struct_0(D_256) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_158])).
% 2.69/1.38  tff(c_163, plain, (![D_256, F_253]: (r1_tmap_1(D_256, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_256), F_253) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_5', F_253) | ~m1_subset_1(F_253, u1_struct_0(D_256)) | ~m1_subset_1(F_253, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_256, '#skF_3') | v2_struct_0(D_256) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_86, c_67, c_28, c_26, c_160])).
% 2.69/1.39  tff(c_183, plain, (![D_257, F_258]: (r1_tmap_1(D_257, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_257), F_258) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_5', F_258) | ~m1_subset_1(F_258, u1_struct_0(D_257)) | ~m1_subset_1(F_258, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_257, '#skF_3') | v2_struct_0(D_257))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_163])).
% 2.69/1.39  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.39  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.39  tff(c_111, plain, (![C_249, A_246, D_245, B_247, E_248]: (k3_tmap_1(A_246, B_247, C_249, D_245, E_248)=k2_partfun1(u1_struct_0(C_249), u1_struct_0(B_247), E_248, u1_struct_0(D_245)) | ~m1_pre_topc(D_245, C_249) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249), u1_struct_0(B_247)))) | ~v1_funct_2(E_248, u1_struct_0(C_249), u1_struct_0(B_247)) | ~v1_funct_1(E_248) | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc(C_249, A_246) | ~l1_pre_topc(B_247) | ~v2_pre_topc(B_247) | v2_struct_0(B_247) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.39  tff(c_113, plain, (![A_246, D_245]: (k3_tmap_1(A_246, '#skF_2', '#skF_3', D_245, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_245)) | ~m1_pre_topc(D_245, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc('#skF_3', A_246) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(resolution, [status(thm)], [c_24, c_111])).
% 2.69/1.39  tff(c_116, plain, (![A_246, D_245]: (k3_tmap_1(A_246, '#skF_2', '#skF_3', D_245, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_245)) | ~m1_pre_topc(D_245, '#skF_3') | ~m1_pre_topc(D_245, A_246) | ~m1_pre_topc('#skF_3', A_246) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_26, c_113])).
% 2.69/1.39  tff(c_118, plain, (![A_250, D_251]: (k3_tmap_1(A_250, '#skF_2', '#skF_3', D_251, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_251)) | ~m1_pre_topc(D_251, '#skF_3') | ~m1_pre_topc(D_251, A_250) | ~m1_pre_topc('#skF_3', A_250) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(negUnitSimplification, [status(thm)], [c_42, c_116])).
% 2.69/1.39  tff(c_122, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_118])).
% 2.69/1.39  tff(c_131, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_16, c_122])).
% 2.69/1.39  tff(c_132, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_131])).
% 2.69/1.39  tff(c_95, plain, (![A_240, B_241, C_242, D_243]: (k2_partfun1(u1_struct_0(A_240), u1_struct_0(B_241), C_242, u1_struct_0(D_243))=k2_tmap_1(A_240, B_241, C_242, D_243) | ~m1_pre_topc(D_243, A_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), u1_struct_0(B_241)))) | ~v1_funct_2(C_242, u1_struct_0(A_240), u1_struct_0(B_241)) | ~v1_funct_1(C_242) | ~l1_pre_topc(B_241) | ~v2_pre_topc(B_241) | v2_struct_0(B_241) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.39  tff(c_97, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.69/1.39  tff(c_100, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_67, c_40, c_38, c_28, c_26, c_97])).
% 2.69/1.39  tff(c_101, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_243) | ~m1_pre_topc(D_243, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_42, c_100])).
% 2.69/1.39  tff(c_140, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_132, c_101])).
% 2.69/1.39  tff(c_147, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_140])).
% 2.69/1.39  tff(c_12, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.69/1.39  tff(c_50, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12])).
% 2.69/1.39  tff(c_152, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_50])).
% 2.69/1.39  tff(c_186, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_183, c_152])).
% 2.69/1.39  tff(c_189, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22, c_49, c_14, c_186])).
% 2.69/1.39  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_189])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 27
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 1
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 1
% 2.69/1.39  #Demod        : 51
% 2.69/1.39  #Tautology    : 15
% 2.69/1.39  #SimpNegUnit  : 7
% 2.69/1.39  #BackRed      : 2
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.37
% 2.69/1.39  Parsing              : 0.19
% 2.69/1.39  CNF conversion       : 0.05
% 2.69/1.39  Main loop            : 0.19
% 2.69/1.39  Inferencing          : 0.07
% 2.69/1.39  Reduction            : 0.07
% 2.69/1.39  Demodulation         : 0.05
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.39  Subsumption          : 0.03
% 2.69/1.39  Abstraction          : 0.01
% 2.69/1.39  MUC search           : 0.00
% 2.69/1.39  Cooper               : 0.00
% 2.69/1.39  Total                : 0.60
% 2.69/1.39  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
