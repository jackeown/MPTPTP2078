%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:17 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :  130 (2306 expanded)
%              Number of leaves         :   32 ( 932 expanded)
%              Depth                    :   23
%              Number of atoms          :  530 (19109 expanded)
%              Number of equality atoms :   31 ( 348 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_252,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(D,C)
                            & m1_pre_topc(E,D) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_205,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_116,axiom,(
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

tff(f_84,axiom,(
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

tff(f_146,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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

tff(f_193,axiom,(
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
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_32,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_90,plain,(
    ! [B_191,A_192] :
      ( v2_pre_topc(B_191)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_111,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_96])).

tff(c_59,plain,(
    ! [B_189,A_190] :
      ( l1_pre_topc(B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_65])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_121,plain,(
    ! [C_193,A_194,B_195] :
      ( m1_pre_topc(C_193,A_194)
      | ~ m1_pre_topc(C_193,B_195)
      | ~ m1_pre_topc(B_195,A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_136,plain,(
    ! [A_194] :
      ( m1_pre_topc('#skF_5',A_194)
      | ~ m1_pre_topc('#skF_4',A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_379,plain,(
    ! [E_239,B_242,D_241,A_238,C_240] :
      ( k3_tmap_1(A_238,B_242,C_240,D_241,E_239) = k2_partfun1(u1_struct_0(C_240),u1_struct_0(B_242),E_239,u1_struct_0(D_241))
      | ~ m1_pre_topc(D_241,C_240)
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(B_242))))
      | ~ v1_funct_2(E_239,u1_struct_0(C_240),u1_struct_0(B_242))
      | ~ v1_funct_1(E_239)
      | ~ m1_pre_topc(D_241,A_238)
      | ~ m1_pre_topc(C_240,A_238)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_383,plain,(
    ! [A_238,D_241] :
      ( k3_tmap_1(A_238,'#skF_2','#skF_3',D_241,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_241))
      | ~ m1_pre_topc(D_241,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_241,A_238)
      | ~ m1_pre_topc('#skF_3',A_238)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_26,c_379])).

tff(c_387,plain,(
    ! [A_238,D_241] :
      ( k3_tmap_1(A_238,'#skF_2','#skF_3',D_241,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_241))
      | ~ m1_pre_topc(D_241,'#skF_3')
      | ~ m1_pre_topc(D_241,A_238)
      | ~ m1_pre_topc('#skF_3',A_238)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_383])).

tff(c_389,plain,(
    ! [A_243,D_244] :
      ( k3_tmap_1(A_243,'#skF_2','#skF_3',D_244,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_244))
      | ~ m1_pre_topc(D_244,'#skF_3')
      | ~ m1_pre_topc(D_244,A_243)
      | ~ m1_pre_topc('#skF_3',A_243)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_387])).

tff(c_403,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_389])).

tff(c_423,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_403])).

tff(c_424,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_423])).

tff(c_534,plain,(
    ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_537,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_534])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_80,c_34,c_537])).

tff(c_546,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_93,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_108,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_93])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_77,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_397,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_389])).

tff(c_411,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_34,c_397])).

tff(c_412,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_411])).

tff(c_342,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( k2_partfun1(u1_struct_0(A_221),u1_struct_0(B_222),C_223,u1_struct_0(D_224)) = k2_tmap_1(A_221,B_222,C_223,D_224)
      | ~ m1_pre_topc(D_224,A_221)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_221),u1_struct_0(B_222))))
      | ~ v1_funct_2(C_223,u1_struct_0(A_221),u1_struct_0(B_222))
      | ~ v1_funct_1(C_223)
      | ~ l1_pre_topc(B_222)
      | ~ v2_pre_topc(B_222)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_344,plain,(
    ! [D_224] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_224)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224)
      | ~ m1_pre_topc(D_224,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_342])).

tff(c_347,plain,(
    ! [D_224] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_224)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224)
      | ~ m1_pre_topc(D_224,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_80,c_50,c_48,c_30,c_28,c_344])).

tff(c_348,plain,(
    ! [D_224] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_224)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224)
      | ~ m1_pre_topc(D_224,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_347])).

tff(c_432,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_348])).

tff(c_439,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_432])).

tff(c_334,plain,(
    ! [D_217,A_216,B_214,C_218,E_215] :
      ( v1_funct_1(k3_tmap_1(A_216,B_214,C_218,D_217,E_215))
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_218),u1_struct_0(B_214))))
      | ~ v1_funct_2(E_215,u1_struct_0(C_218),u1_struct_0(B_214))
      | ~ v1_funct_1(E_215)
      | ~ m1_pre_topc(D_217,A_216)
      | ~ m1_pre_topc(C_218,A_216)
      | ~ l1_pre_topc(B_214)
      | ~ v2_pre_topc(B_214)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_336,plain,(
    ! [A_216,D_217] :
      ( v1_funct_1(k3_tmap_1(A_216,'#skF_2','#skF_3',D_217,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_217,A_216)
      | ~ m1_pre_topc('#skF_3',A_216)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_26,c_334])).

tff(c_339,plain,(
    ! [A_216,D_217] :
      ( v1_funct_1(k3_tmap_1(A_216,'#skF_2','#skF_3',D_217,'#skF_6'))
      | ~ m1_pre_topc(D_217,A_216)
      | ~ m1_pre_topc('#skF_3',A_216)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_336])).

tff(c_340,plain,(
    ! [A_216,D_217] :
      ( v1_funct_1(k3_tmap_1(A_216,'#skF_2','#skF_3',D_217,'#skF_6'))
      | ~ m1_pre_topc(D_217,A_216)
      | ~ m1_pre_topc('#skF_3',A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_339])).

tff(c_462,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_340])).

tff(c_472,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_40,c_462])).

tff(c_473,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_472])).

tff(c_358,plain,(
    ! [E_227,A_228,B_226,C_230,D_229] :
      ( v1_funct_2(k3_tmap_1(A_228,B_226,C_230,D_229,E_227),u1_struct_0(D_229),u1_struct_0(B_226))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_226))))
      | ~ v1_funct_2(E_227,u1_struct_0(C_230),u1_struct_0(B_226))
      | ~ v1_funct_1(E_227)
      | ~ m1_pre_topc(D_229,A_228)
      | ~ m1_pre_topc(C_230,A_228)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_360,plain,(
    ! [A_228,D_229] :
      ( v1_funct_2(k3_tmap_1(A_228,'#skF_2','#skF_3',D_229,'#skF_6'),u1_struct_0(D_229),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_229,A_228)
      | ~ m1_pre_topc('#skF_3',A_228)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_26,c_358])).

tff(c_363,plain,(
    ! [A_228,D_229] :
      ( v1_funct_2(k3_tmap_1(A_228,'#skF_2','#skF_3',D_229,'#skF_6'),u1_struct_0(D_229),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_229,A_228)
      | ~ m1_pre_topc('#skF_3',A_228)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_360])).

tff(c_364,plain,(
    ! [A_228,D_229] :
      ( v1_funct_2(k3_tmap_1(A_228,'#skF_2','#skF_3',D_229,'#skF_6'),u1_struct_0(D_229),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_229,A_228)
      | ~ m1_pre_topc('#skF_3',A_228)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_363])).

tff(c_459,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_364])).

tff(c_469,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_40,c_459])).

tff(c_470,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_469])).

tff(c_14,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( m1_subset_1(k3_tmap_1(A_57,B_58,C_59,D_60,E_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60),u1_struct_0(B_58))))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_456,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_14])).

tff(c_466,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_44,c_40,c_30,c_28,c_26,c_456])).

tff(c_467,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_466])).

tff(c_10,plain,(
    ! [A_11,B_19,C_23,D_25] :
      ( k2_partfun1(u1_struct_0(A_11),u1_struct_0(B_19),C_23,u1_struct_0(D_25)) = k2_tmap_1(A_11,B_19,C_23,D_25)
      | ~ m1_pre_topc(D_25,A_11)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11),u1_struct_0(B_19))))
      | ~ v1_funct_2(C_23,u1_struct_0(A_11),u1_struct_0(B_19))
      | ~ v1_funct_1(C_23)
      | ~ l1_pre_topc(B_19)
      | ~ v2_pre_topc(B_19)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_482,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_467,c_10])).

tff(c_497,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_77,c_50,c_48,c_473,c_470,c_482])).

tff(c_498,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_497])).

tff(c_12,plain,(
    ! [A_26,C_50,B_42,D_54,E_56] :
      ( k3_tmap_1(A_26,B_42,C_50,D_54,E_56) = k2_partfun1(u1_struct_0(C_50),u1_struct_0(B_42),E_56,u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,C_50)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_50),u1_struct_0(B_42))))
      | ~ v1_funct_2(E_56,u1_struct_0(C_50),u1_struct_0(B_42))
      | ~ v1_funct_1(E_56)
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc(C_50,A_26)
      | ~ l1_pre_topc(B_42)
      | ~ v2_pre_topc(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_478,plain,(
    ! [A_26,D_54] :
      ( k3_tmap_1(A_26,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc('#skF_4',A_26)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_467,c_12])).

tff(c_489,plain,(
    ! [A_26,D_54] :
      ( k3_tmap_1(A_26,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,'#skF_4')
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc('#skF_4',A_26)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_473,c_470,c_478])).

tff(c_1099,plain,(
    ! [A_308,D_309] :
      ( k3_tmap_1(A_308,'#skF_2','#skF_4',D_309,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_309))
      | ~ m1_pre_topc(D_309,'#skF_4')
      | ~ m1_pre_topc(D_309,A_308)
      | ~ m1_pre_topc('#skF_4',A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_489])).

tff(c_1369,plain,(
    ! [A_316,D_317] :
      ( k3_tmap_1(A_316,'#skF_2','#skF_4',D_317,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_317)
      | ~ m1_pre_topc(D_317,'#skF_4')
      | ~ m1_pre_topc(D_317,A_316)
      | ~ m1_pre_topc('#skF_4',A_316)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316)
      | ~ m1_pre_topc(D_317,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_1099])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_486,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_505,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_470,c_486])).

tff(c_20,plain,(
    ! [C_110,F_124,E_122,B_94,D_118,A_62] :
      ( r2_funct_2(u1_struct_0(D_118),u1_struct_0(B_94),k3_tmap_1(A_62,B_94,C_110,D_118,F_124),k2_tmap_1(A_62,B_94,E_122,D_118))
      | ~ m1_pre_topc(D_118,C_110)
      | ~ r2_funct_2(u1_struct_0(C_110),u1_struct_0(B_94),F_124,k2_tmap_1(A_62,B_94,E_122,C_110))
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_110),u1_struct_0(B_94))))
      | ~ v1_funct_2(F_124,u1_struct_0(C_110),u1_struct_0(B_94))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(B_94))))
      | ~ v1_funct_2(E_122,u1_struct_0(A_62),u1_struct_0(B_94))
      | ~ v1_funct_1(E_122)
      | ~ m1_pre_topc(D_118,A_62)
      | v2_struct_0(D_118)
      | ~ m1_pre_topc(C_110,A_62)
      | v2_struct_0(C_110)
      | ~ l1_pre_topc(B_94)
      | ~ v2_pre_topc(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_523,plain,(
    ! [D_118] :
      ( r2_funct_2(u1_struct_0(D_118),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_118,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_118))
      | ~ m1_pre_topc(D_118,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_118,'#skF_3')
      | v2_struct_0(D_118)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_505,c_20])).

tff(c_528,plain,(
    ! [D_118] :
      ( r2_funct_2(u1_struct_0(D_118),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_118,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_118))
      | ~ m1_pre_topc(D_118,'#skF_4')
      | ~ m1_pre_topc(D_118,'#skF_3')
      | v2_struct_0(D_118)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_80,c_50,c_48,c_34,c_30,c_28,c_26,c_473,c_470,c_467,c_523])).

tff(c_529,plain,(
    ! [D_118] :
      ( r2_funct_2(u1_struct_0(D_118),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_118,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_118))
      | ~ m1_pre_topc(D_118,'#skF_4')
      | ~ m1_pre_topc(D_118,'#skF_3')
      | v2_struct_0(D_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_42,c_528])).

tff(c_1383,plain,(
    ! [D_317] :
      ( r2_funct_2(u1_struct_0(D_317),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_317),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_317))
      | ~ m1_pre_topc(D_317,'#skF_4')
      | ~ m1_pre_topc(D_317,'#skF_3')
      | v2_struct_0(D_317)
      | ~ m1_pre_topc(D_317,'#skF_4')
      | ~ m1_pre_topc(D_317,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_317,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_529])).

tff(c_1417,plain,(
    ! [D_317] :
      ( r2_funct_2(u1_struct_0(D_317),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_317),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_317))
      | v2_struct_0(D_317)
      | ~ m1_pre_topc(D_317,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_317,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_80,c_34,c_1383])).

tff(c_1438,plain,(
    ! [D_318] :
      ( r2_funct_2(u1_struct_0(D_318),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_318),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_318))
      | v2_struct_0(D_318)
      | ~ m1_pre_topc(D_318,'#skF_3')
      | ~ m1_pre_topc(D_318,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1417])).

tff(c_545,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_638,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_348])).

tff(c_645,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_638])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_452,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_24])).

tff(c_819,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_452])).

tff(c_1395,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_819])).

tff(c_1423,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_54,c_40,c_36,c_32,c_1395])).

tff(c_1424,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1423])).

tff(c_1441,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1438,c_1424])).

tff(c_1448,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_546,c_1441])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.96  
% 4.74/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.96  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.74/1.96  
% 4.74/1.96  %Foreground sorts:
% 4.74/1.96  
% 4.74/1.96  
% 4.74/1.96  %Background operators:
% 4.74/1.96  
% 4.74/1.96  
% 4.74/1.96  %Foreground operators:
% 4.74/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.74/1.96  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.74/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.74/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.74/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.96  tff('#skF_6', type, '#skF_6': $i).
% 4.74/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.96  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.74/1.96  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.74/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.74/1.96  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.74/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.74/1.96  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.74/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.96  
% 5.08/1.99  tff(f_252, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 5.08/1.99  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.08/1.99  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.08/1.99  tff(f_205, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 5.08/1.99  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.08/1.99  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.08/1.99  tff(f_146, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 5.08/1.99  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.08/1.99  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tmap_1)).
% 5.08/1.99  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_32, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_90, plain, (![B_191, A_192]: (v2_pre_topc(B_191) | ~m1_pre_topc(B_191, A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.08/1.99  tff(c_96, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_90])).
% 5.08/1.99  tff(c_111, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_96])).
% 5.08/1.99  tff(c_59, plain, (![B_189, A_190]: (l1_pre_topc(B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.08/1.99  tff(c_65, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_59])).
% 5.08/1.99  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_65])).
% 5.08/1.99  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_121, plain, (![C_193, A_194, B_195]: (m1_pre_topc(C_193, A_194) | ~m1_pre_topc(C_193, B_195) | ~m1_pre_topc(B_195, A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.08/1.99  tff(c_136, plain, (![A_194]: (m1_pre_topc('#skF_5', A_194) | ~m1_pre_topc('#skF_4', A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(resolution, [status(thm)], [c_32, c_121])).
% 5.08/1.99  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_28, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_379, plain, (![E_239, B_242, D_241, A_238, C_240]: (k3_tmap_1(A_238, B_242, C_240, D_241, E_239)=k2_partfun1(u1_struct_0(C_240), u1_struct_0(B_242), E_239, u1_struct_0(D_241)) | ~m1_pre_topc(D_241, C_240) | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240), u1_struct_0(B_242)))) | ~v1_funct_2(E_239, u1_struct_0(C_240), u1_struct_0(B_242)) | ~v1_funct_1(E_239) | ~m1_pre_topc(D_241, A_238) | ~m1_pre_topc(C_240, A_238) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.08/1.99  tff(c_383, plain, (![A_238, D_241]: (k3_tmap_1(A_238, '#skF_2', '#skF_3', D_241, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_241)) | ~m1_pre_topc(D_241, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_241, A_238) | ~m1_pre_topc('#skF_3', A_238) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_26, c_379])).
% 5.08/1.99  tff(c_387, plain, (![A_238, D_241]: (k3_tmap_1(A_238, '#skF_2', '#skF_3', D_241, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_241)) | ~m1_pre_topc(D_241, '#skF_3') | ~m1_pre_topc(D_241, A_238) | ~m1_pre_topc('#skF_3', A_238) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_383])).
% 5.08/1.99  tff(c_389, plain, (![A_243, D_244]: (k3_tmap_1(A_243, '#skF_2', '#skF_3', D_244, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_244)) | ~m1_pre_topc(D_244, '#skF_3') | ~m1_pre_topc(D_244, A_243) | ~m1_pre_topc('#skF_3', A_243) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(negUnitSimplification, [status(thm)], [c_52, c_387])).
% 5.08/1.99  tff(c_403, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_389])).
% 5.08/1.99  tff(c_423, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_403])).
% 5.08/1.99  tff(c_424, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_423])).
% 5.08/1.99  tff(c_534, plain, (~m1_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_424])).
% 5.08/1.99  tff(c_537, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_136, c_534])).
% 5.08/1.99  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_80, c_34, c_537])).
% 5.08/1.99  tff(c_546, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_424])).
% 5.08/1.99  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_93, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_90])).
% 5.08/1.99  tff(c_108, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_93])).
% 5.08/1.99  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_59])).
% 5.08/1.99  tff(c_77, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 5.08/1.99  tff(c_397, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_389])).
% 5.08/1.99  tff(c_411, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_34, c_397])).
% 5.08/1.99  tff(c_412, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_411])).
% 5.08/1.99  tff(c_342, plain, (![A_221, B_222, C_223, D_224]: (k2_partfun1(u1_struct_0(A_221), u1_struct_0(B_222), C_223, u1_struct_0(D_224))=k2_tmap_1(A_221, B_222, C_223, D_224) | ~m1_pre_topc(D_224, A_221) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_221), u1_struct_0(B_222)))) | ~v1_funct_2(C_223, u1_struct_0(A_221), u1_struct_0(B_222)) | ~v1_funct_1(C_223) | ~l1_pre_topc(B_222) | ~v2_pre_topc(B_222) | v2_struct_0(B_222) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.08/1.99  tff(c_344, plain, (![D_224]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_224))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224) | ~m1_pre_topc(D_224, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_342])).
% 5.08/1.99  tff(c_347, plain, (![D_224]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_224))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224) | ~m1_pre_topc(D_224, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_80, c_50, c_48, c_30, c_28, c_344])).
% 5.08/1.99  tff(c_348, plain, (![D_224]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_224))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224) | ~m1_pre_topc(D_224, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_347])).
% 5.08/1.99  tff(c_432, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_412, c_348])).
% 5.08/1.99  tff(c_439, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_432])).
% 5.08/1.99  tff(c_334, plain, (![D_217, A_216, B_214, C_218, E_215]: (v1_funct_1(k3_tmap_1(A_216, B_214, C_218, D_217, E_215)) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_218), u1_struct_0(B_214)))) | ~v1_funct_2(E_215, u1_struct_0(C_218), u1_struct_0(B_214)) | ~v1_funct_1(E_215) | ~m1_pre_topc(D_217, A_216) | ~m1_pre_topc(C_218, A_216) | ~l1_pre_topc(B_214) | ~v2_pre_topc(B_214) | v2_struct_0(B_214) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.08/1.99  tff(c_336, plain, (![A_216, D_217]: (v1_funct_1(k3_tmap_1(A_216, '#skF_2', '#skF_3', D_217, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_217, A_216) | ~m1_pre_topc('#skF_3', A_216) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_26, c_334])).
% 5.08/1.99  tff(c_339, plain, (![A_216, D_217]: (v1_funct_1(k3_tmap_1(A_216, '#skF_2', '#skF_3', D_217, '#skF_6')) | ~m1_pre_topc(D_217, A_216) | ~m1_pre_topc('#skF_3', A_216) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_336])).
% 5.08/1.99  tff(c_340, plain, (![A_216, D_217]: (v1_funct_1(k3_tmap_1(A_216, '#skF_2', '#skF_3', D_217, '#skF_6')) | ~m1_pre_topc(D_217, A_216) | ~m1_pre_topc('#skF_3', A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(negUnitSimplification, [status(thm)], [c_52, c_339])).
% 5.08/1.99  tff(c_462, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_439, c_340])).
% 5.08/1.99  tff(c_472, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_40, c_462])).
% 5.08/1.99  tff(c_473, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_472])).
% 5.08/1.99  tff(c_358, plain, (![E_227, A_228, B_226, C_230, D_229]: (v1_funct_2(k3_tmap_1(A_228, B_226, C_230, D_229, E_227), u1_struct_0(D_229), u1_struct_0(B_226)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_226)))) | ~v1_funct_2(E_227, u1_struct_0(C_230), u1_struct_0(B_226)) | ~v1_funct_1(E_227) | ~m1_pre_topc(D_229, A_228) | ~m1_pre_topc(C_230, A_228) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.08/1.99  tff(c_360, plain, (![A_228, D_229]: (v1_funct_2(k3_tmap_1(A_228, '#skF_2', '#skF_3', D_229, '#skF_6'), u1_struct_0(D_229), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_229, A_228) | ~m1_pre_topc('#skF_3', A_228) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_26, c_358])).
% 5.08/1.99  tff(c_363, plain, (![A_228, D_229]: (v1_funct_2(k3_tmap_1(A_228, '#skF_2', '#skF_3', D_229, '#skF_6'), u1_struct_0(D_229), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_229, A_228) | ~m1_pre_topc('#skF_3', A_228) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_360])).
% 5.08/1.99  tff(c_364, plain, (![A_228, D_229]: (v1_funct_2(k3_tmap_1(A_228, '#skF_2', '#skF_3', D_229, '#skF_6'), u1_struct_0(D_229), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_229, A_228) | ~m1_pre_topc('#skF_3', A_228) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(negUnitSimplification, [status(thm)], [c_52, c_363])).
% 5.08/1.99  tff(c_459, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_439, c_364])).
% 5.08/1.99  tff(c_469, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_40, c_459])).
% 5.08/1.99  tff(c_470, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_469])).
% 5.08/1.99  tff(c_14, plain, (![A_57, E_61, B_58, D_60, C_59]: (m1_subset_1(k3_tmap_1(A_57, B_58, C_59, D_60, E_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60), u1_struct_0(B_58)))) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.08/1.99  tff(c_456, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_439, c_14])).
% 5.08/1.99  tff(c_466, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_44, c_40, c_30, c_28, c_26, c_456])).
% 5.08/1.99  tff(c_467, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_466])).
% 5.08/1.99  tff(c_10, plain, (![A_11, B_19, C_23, D_25]: (k2_partfun1(u1_struct_0(A_11), u1_struct_0(B_19), C_23, u1_struct_0(D_25))=k2_tmap_1(A_11, B_19, C_23, D_25) | ~m1_pre_topc(D_25, A_11) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11), u1_struct_0(B_19)))) | ~v1_funct_2(C_23, u1_struct_0(A_11), u1_struct_0(B_19)) | ~v1_funct_1(C_23) | ~l1_pre_topc(B_19) | ~v2_pre_topc(B_19) | v2_struct_0(B_19) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.08/1.99  tff(c_482, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_467, c_10])).
% 5.08/1.99  tff(c_497, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_77, c_50, c_48, c_473, c_470, c_482])).
% 5.08/1.99  tff(c_498, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_497])).
% 5.08/1.99  tff(c_12, plain, (![A_26, C_50, B_42, D_54, E_56]: (k3_tmap_1(A_26, B_42, C_50, D_54, E_56)=k2_partfun1(u1_struct_0(C_50), u1_struct_0(B_42), E_56, u1_struct_0(D_54)) | ~m1_pre_topc(D_54, C_50) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_50), u1_struct_0(B_42)))) | ~v1_funct_2(E_56, u1_struct_0(C_50), u1_struct_0(B_42)) | ~v1_funct_1(E_56) | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc(C_50, A_26) | ~l1_pre_topc(B_42) | ~v2_pre_topc(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.08/1.99  tff(c_478, plain, (![A_26, D_54]: (k3_tmap_1(A_26, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_54)) | ~m1_pre_topc(D_54, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc('#skF_4', A_26) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_467, c_12])).
% 5.08/1.99  tff(c_489, plain, (![A_26, D_54]: (k3_tmap_1(A_26, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_54)) | ~m1_pre_topc(D_54, '#skF_4') | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc('#skF_4', A_26) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_473, c_470, c_478])).
% 5.08/1.99  tff(c_1099, plain, (![A_308, D_309]: (k3_tmap_1(A_308, '#skF_2', '#skF_4', D_309, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_309)) | ~m1_pre_topc(D_309, '#skF_4') | ~m1_pre_topc(D_309, A_308) | ~m1_pre_topc('#skF_4', A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(negUnitSimplification, [status(thm)], [c_52, c_489])).
% 5.08/1.99  tff(c_1369, plain, (![A_316, D_317]: (k3_tmap_1(A_316, '#skF_2', '#skF_4', D_317, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_317) | ~m1_pre_topc(D_317, '#skF_4') | ~m1_pre_topc(D_317, A_316) | ~m1_pre_topc('#skF_4', A_316) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316) | ~m1_pre_topc(D_317, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_498, c_1099])).
% 5.08/1.99  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.08/1.99  tff(c_486, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_467, c_2])).
% 5.08/1.99  tff(c_505, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_470, c_486])).
% 5.08/1.99  tff(c_20, plain, (![C_110, F_124, E_122, B_94, D_118, A_62]: (r2_funct_2(u1_struct_0(D_118), u1_struct_0(B_94), k3_tmap_1(A_62, B_94, C_110, D_118, F_124), k2_tmap_1(A_62, B_94, E_122, D_118)) | ~m1_pre_topc(D_118, C_110) | ~r2_funct_2(u1_struct_0(C_110), u1_struct_0(B_94), F_124, k2_tmap_1(A_62, B_94, E_122, C_110)) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_110), u1_struct_0(B_94)))) | ~v1_funct_2(F_124, u1_struct_0(C_110), u1_struct_0(B_94)) | ~v1_funct_1(F_124) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62), u1_struct_0(B_94)))) | ~v1_funct_2(E_122, u1_struct_0(A_62), u1_struct_0(B_94)) | ~v1_funct_1(E_122) | ~m1_pre_topc(D_118, A_62) | v2_struct_0(D_118) | ~m1_pre_topc(C_110, A_62) | v2_struct_0(C_110) | ~l1_pre_topc(B_94) | ~v2_pre_topc(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.08/1.99  tff(c_523, plain, (![D_118]: (r2_funct_2(u1_struct_0(D_118), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_118, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_118)) | ~m1_pre_topc(D_118, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_118, '#skF_3') | v2_struct_0(D_118) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_505, c_20])).
% 5.08/1.99  tff(c_528, plain, (![D_118]: (r2_funct_2(u1_struct_0(D_118), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_118, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_118)) | ~m1_pre_topc(D_118, '#skF_4') | ~m1_pre_topc(D_118, '#skF_3') | v2_struct_0(D_118) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_80, c_50, c_48, c_34, c_30, c_28, c_26, c_473, c_470, c_467, c_523])).
% 5.08/1.99  tff(c_529, plain, (![D_118]: (r2_funct_2(u1_struct_0(D_118), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_118, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_118)) | ~m1_pre_topc(D_118, '#skF_4') | ~m1_pre_topc(D_118, '#skF_3') | v2_struct_0(D_118))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_42, c_528])).
% 5.08/1.99  tff(c_1383, plain, (![D_317]: (r2_funct_2(u1_struct_0(D_317), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_317), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_317)) | ~m1_pre_topc(D_317, '#skF_4') | ~m1_pre_topc(D_317, '#skF_3') | v2_struct_0(D_317) | ~m1_pre_topc(D_317, '#skF_4') | ~m1_pre_topc(D_317, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_317, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1369, c_529])).
% 5.08/1.99  tff(c_1417, plain, (![D_317]: (r2_funct_2(u1_struct_0(D_317), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_317), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_317)) | v2_struct_0(D_317) | ~m1_pre_topc(D_317, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_317, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_80, c_34, c_1383])).
% 5.08/1.99  tff(c_1438, plain, (![D_318]: (r2_funct_2(u1_struct_0(D_318), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_318), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_318)) | v2_struct_0(D_318) | ~m1_pre_topc(D_318, '#skF_3') | ~m1_pre_topc(D_318, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1417])).
% 5.08/1.99  tff(c_545, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_424])).
% 5.08/1.99  tff(c_638, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_348])).
% 5.08/1.99  tff(c_645, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_638])).
% 5.08/1.99  tff(c_24, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.08/1.99  tff(c_452, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_24])).
% 5.08/1.99  tff(c_819, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_452])).
% 5.08/1.99  tff(c_1395, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1369, c_819])).
% 5.08/1.99  tff(c_1423, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_54, c_40, c_36, c_32, c_1395])).
% 5.08/1.99  tff(c_1424, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1423])).
% 5.08/1.99  tff(c_1441, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1438, c_1424])).
% 5.08/1.99  tff(c_1448, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_546, c_1441])).
% 5.08/1.99  tff(c_1450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1448])).
% 5.08/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.99  
% 5.08/1.99  Inference rules
% 5.08/1.99  ----------------------
% 5.08/1.99  #Ref     : 0
% 5.08/1.99  #Sup     : 267
% 5.08/1.99  #Fact    : 0
% 5.08/1.99  #Define  : 0
% 5.08/1.99  #Split   : 7
% 5.08/1.99  #Chain   : 0
% 5.08/1.99  #Close   : 0
% 5.08/1.99  
% 5.08/1.99  Ordering : KBO
% 5.08/1.99  
% 5.08/1.99  Simplification rules
% 5.08/1.99  ----------------------
% 5.08/1.99  #Subsume      : 54
% 5.08/1.99  #Demod        : 747
% 5.08/1.99  #Tautology    : 78
% 5.08/1.99  #SimpNegUnit  : 99
% 5.08/1.99  #BackRed      : 3
% 5.08/1.99  
% 5.08/1.99  #Partial instantiations: 0
% 5.08/1.99  #Strategies tried      : 1
% 5.08/1.99  
% 5.08/1.99  Timing (in seconds)
% 5.08/1.99  ----------------------
% 5.08/1.99  Preprocessing        : 0.36
% 5.08/1.99  Parsing              : 0.19
% 5.08/1.99  CNF conversion       : 0.05
% 5.08/1.99  Main loop            : 0.77
% 5.08/1.99  Inferencing          : 0.22
% 5.08/1.99  Reduction            : 0.28
% 5.08/1.99  Demodulation         : 0.21
% 5.08/1.99  BG Simplification    : 0.03
% 5.08/1.99  Subsumption          : 0.19
% 5.08/1.99  Abstraction          : 0.04
% 5.08/1.99  MUC search           : 0.00
% 5.08/1.99  Cooper               : 0.00
% 5.08/1.99  Total                : 1.19
% 5.08/1.99  Index Insertion      : 0.00
% 5.08/1.99  Index Deletion       : 0.00
% 5.08/1.99  Index Matching       : 0.00
% 5.08/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
