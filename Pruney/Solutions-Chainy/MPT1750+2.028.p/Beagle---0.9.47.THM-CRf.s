%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 361 expanded)
%              Number of leaves         :   42 ( 130 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 (1433 expanded)
%              Number of equality atoms :   37 ( 378 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
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
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_125,axiom,(
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

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_112,plain,(
    ! [D_80,B_81,C_82,A_83] :
      ( D_80 = B_81
      | g1_pre_topc(C_82,D_80) != g1_pre_topc(A_83,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    ! [D_80,C_82] :
      ( u1_pre_topc('#skF_2') = D_80
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_82,D_80)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_112])).

tff(c_171,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_171])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_175])).

tff(c_180,plain,(
    ! [D_80,C_82] :
      ( u1_pre_topc('#skF_2') = D_80
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_82,D_80) ) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_198,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_180])).

tff(c_181,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_206,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_181])).

tff(c_207,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_32])).

tff(c_24,plain,(
    ! [C_22,A_18,D_23,B_19] :
      ( C_22 = A_18
      | g1_pre_topc(C_22,D_23) != g1_pre_topc(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_244,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_24])).

tff(c_250,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_244])).

tff(c_279,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_250])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_154,plain,(
    ! [A_98,F_97,D_99,B_95,C_94,E_96] :
      ( r1_funct_2(A_98,B_95,C_94,D_99,E_96,E_96)
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(C_94,D_99)))
      | ~ v1_funct_2(F_97,C_94,D_99)
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_95)))
      | ~ v1_funct_2(E_96,A_98,B_95)
      | ~ v1_funct_1(E_96)
      | v1_xboole_0(D_99)
      | v1_xboole_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_156,plain,(
    ! [A_98,B_95,E_96] :
      ( r1_funct_2(A_98,B_95,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_96,E_96)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_95)))
      | ~ v1_funct_2(E_96,A_98,B_95)
      | ~ v1_funct_1(E_96)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_95) ) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_159,plain,(
    ! [A_98,B_95,E_96] :
      ( r1_funct_2(A_98,B_95,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_96,E_96)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_95)))
      | ~ v1_funct_2(E_96,A_98,B_95)
      | ~ v1_funct_1(E_96)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_156])).

tff(c_353,plain,(
    ! [A_98,B_95,E_96] :
      ( r1_funct_2(A_98,B_95,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_96,E_96)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_95)))
      | ~ v1_funct_2(E_96,A_98,B_95)
      | ~ v1_funct_1(E_96)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_159])).

tff(c_354,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_20,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_357,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_354,c_20])).

tff(c_360,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_357])).

tff(c_363,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_360])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_363])).

tff(c_369,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_294,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_36])).

tff(c_293,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_34])).

tff(c_430,plain,(
    ! [A_118,B_119,E_120] :
      ( r1_funct_2(A_118,B_119,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_120,E_120)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(E_120,A_118,B_119)
      | ~ v1_funct_1(E_120)
      | v1_xboole_0(B_119) ) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_57,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_62,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_72,A_73] :
      ( k7_relat_1(B_72,A_73) = B_72
      | ~ r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_91,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_88])).

tff(c_94,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_91])).

tff(c_291,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_94])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_122,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [D_89] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_127,plain,(
    ! [D_89] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124])).

tff(c_228,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k2_partfun1(u1_struct_0(A_103),u1_struct_0(B_104),C_105,u1_struct_0(D_106)) = k2_tmap_1(A_103,B_104,C_105,D_106)
      | ~ m1_pre_topc(D_106,A_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc(B_104)
      | ~ v2_pre_topc(B_104)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_230,plain,(
    ! [D_106] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_106)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_106)
      | ~ m1_pre_topc(D_106,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_233,plain,(
    ! [D_106] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_106)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_106)
      | ~ m1_pre_topc(D_106,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_52,c_50,c_38,c_36,c_127,c_230])).

tff(c_234,plain,(
    ! [D_106] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_106)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_106)
      | ~ m1_pre_topc(D_106,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_233])).

tff(c_331,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_234])).

tff(c_338,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_30,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_290,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_30])).

tff(c_423,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_290])).

tff(c_433,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_430,c_423])).

tff(c_436,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_294,c_293,c_433])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.44  
% 2.57/1.44  %Foreground sorts:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Background operators:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Foreground operators:
% 2.57/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.57/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.44  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.57/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.57/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.44  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.90/1.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.90/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.44  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.90/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.44  
% 2.90/1.46  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.90/1.46  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.90/1.46  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.90/1.46  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.90/1.46  tff(f_98, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.90/1.46  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.90/1.46  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.46  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.46  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.46  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.90/1.46  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.90/1.46  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.90/1.46  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.46  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.46  tff(c_32, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_112, plain, (![D_80, B_81, C_82, A_83]: (D_80=B_81 | g1_pre_topc(C_82, D_80)!=g1_pre_topc(A_83, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_116, plain, (![D_80, C_82]: (u1_pre_topc('#skF_2')=D_80 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_82, D_80) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_112])).
% 2.90/1.46  tff(c_171, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_116])).
% 2.90/1.46  tff(c_175, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_171])).
% 2.90/1.46  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_175])).
% 2.90/1.46  tff(c_180, plain, (![D_80, C_82]: (u1_pre_topc('#skF_2')=D_80 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_82, D_80))), inference(splitRight, [status(thm)], [c_116])).
% 2.90/1.46  tff(c_198, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_180])).
% 2.90/1.46  tff(c_181, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_116])).
% 2.90/1.46  tff(c_206, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_181])).
% 2.90/1.46  tff(c_207, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_32])).
% 2.90/1.46  tff(c_24, plain, (![C_22, A_18, D_23, B_19]: (C_22=A_18 | g1_pre_topc(C_22, D_23)!=g1_pre_topc(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_244, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_207, c_24])).
% 2.90/1.46  tff(c_250, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_244])).
% 2.90/1.46  tff(c_279, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_250])).
% 2.90/1.46  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_154, plain, (![A_98, F_97, D_99, B_95, C_94, E_96]: (r1_funct_2(A_98, B_95, C_94, D_99, E_96, E_96) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(C_94, D_99))) | ~v1_funct_2(F_97, C_94, D_99) | ~v1_funct_1(F_97) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_95))) | ~v1_funct_2(E_96, A_98, B_95) | ~v1_funct_1(E_96) | v1_xboole_0(D_99) | v1_xboole_0(B_95))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.90/1.46  tff(c_156, plain, (![A_98, B_95, E_96]: (r1_funct_2(A_98, B_95, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_96, E_96) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_95))) | ~v1_funct_2(E_96, A_98, B_95) | ~v1_funct_1(E_96) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_95))), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.90/1.46  tff(c_159, plain, (![A_98, B_95, E_96]: (r1_funct_2(A_98, B_95, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_96, E_96) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_95))) | ~v1_funct_2(E_96, A_98, B_95) | ~v1_funct_1(E_96) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_156])).
% 2.90/1.46  tff(c_353, plain, (![A_98, B_95, E_96]: (r1_funct_2(A_98, B_95, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_96, E_96) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_95))) | ~v1_funct_2(E_96, A_98, B_95) | ~v1_funct_1(E_96) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_159])).
% 2.90/1.46  tff(c_354, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_353])).
% 2.90/1.46  tff(c_20, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.46  tff(c_357, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_354, c_20])).
% 2.90/1.46  tff(c_360, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_357])).
% 2.90/1.46  tff(c_363, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_360])).
% 2.90/1.46  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_363])).
% 2.90/1.46  tff(c_369, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_353])).
% 2.90/1.46  tff(c_294, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_36])).
% 2.90/1.46  tff(c_293, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_34])).
% 2.90/1.46  tff(c_430, plain, (![A_118, B_119, E_120]: (r1_funct_2(A_118, B_119, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_120, E_120) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(E_120, A_118, B_119) | ~v1_funct_1(E_120) | v1_xboole_0(B_119))), inference(splitRight, [status(thm)], [c_353])).
% 2.90/1.46  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_57, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.46  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.90/1.46  tff(c_62, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.46  tff(c_66, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.90/1.46  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.46  tff(c_83, plain, (![B_72, A_73]: (k7_relat_1(B_72, A_73)=B_72 | ~r1_tarski(k1_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.46  tff(c_88, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.90/1.46  tff(c_91, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_88])).
% 2.90/1.46  tff(c_94, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_91])).
% 2.90/1.46  tff(c_291, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_94])).
% 2.90/1.46  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_122, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.90/1.46  tff(c_124, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_122])).
% 2.90/1.46  tff(c_127, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124])).
% 2.90/1.46  tff(c_228, plain, (![A_103, B_104, C_105, D_106]: (k2_partfun1(u1_struct_0(A_103), u1_struct_0(B_104), C_105, u1_struct_0(D_106))=k2_tmap_1(A_103, B_104, C_105, D_106) | ~m1_pre_topc(D_106, A_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0(A_103), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_pre_topc(B_104) | ~v2_pre_topc(B_104) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.46  tff(c_230, plain, (![D_106]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_106))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_106) | ~m1_pre_topc(D_106, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_228])).
% 2.90/1.46  tff(c_233, plain, (![D_106]: (k7_relat_1('#skF_4', u1_struct_0(D_106))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_106) | ~m1_pre_topc(D_106, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_52, c_50, c_38, c_36, c_127, c_230])).
% 2.90/1.46  tff(c_234, plain, (![D_106]: (k7_relat_1('#skF_4', u1_struct_0(D_106))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_106) | ~m1_pre_topc(D_106, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_233])).
% 2.90/1.46  tff(c_331, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_291, c_234])).
% 2.90/1.46  tff(c_338, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_331])).
% 2.90/1.46  tff(c_30, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.90/1.46  tff(c_290, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_30])).
% 2.90/1.46  tff(c_423, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_290])).
% 2.90/1.46  tff(c_433, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_430, c_423])).
% 2.90/1.46  tff(c_436, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_294, c_293, c_433])).
% 2.90/1.46  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_436])).
% 2.90/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  Inference rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Ref     : 8
% 2.90/1.46  #Sup     : 71
% 2.90/1.46  #Fact    : 0
% 2.90/1.46  #Define  : 0
% 2.90/1.46  #Split   : 6
% 2.90/1.46  #Chain   : 0
% 2.90/1.46  #Close   : 0
% 2.90/1.46  
% 2.90/1.46  Ordering : KBO
% 2.90/1.46  
% 2.90/1.46  Simplification rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Subsume      : 13
% 2.90/1.46  #Demod        : 74
% 2.90/1.46  #Tautology    : 42
% 2.90/1.46  #SimpNegUnit  : 9
% 2.90/1.46  #BackRed      : 11
% 2.90/1.46  
% 2.90/1.46  #Partial instantiations: 0
% 2.90/1.46  #Strategies tried      : 1
% 2.90/1.46  
% 2.90/1.46  Timing (in seconds)
% 2.90/1.46  ----------------------
% 2.90/1.47  Preprocessing        : 0.36
% 2.90/1.47  Parsing              : 0.20
% 2.90/1.47  CNF conversion       : 0.03
% 2.90/1.47  Main loop            : 0.29
% 2.90/1.47  Inferencing          : 0.11
% 2.90/1.47  Reduction            : 0.09
% 2.90/1.47  Demodulation         : 0.06
% 2.90/1.47  BG Simplification    : 0.02
% 2.90/1.47  Subsumption          : 0.05
% 2.90/1.47  Abstraction          : 0.01
% 2.90/1.47  MUC search           : 0.00
% 2.90/1.47  Cooper               : 0.00
% 2.90/1.47  Total                : 0.69
% 2.90/1.47  Index Insertion      : 0.00
% 2.90/1.47  Index Deletion       : 0.00
% 2.90/1.47  Index Matching       : 0.00
% 2.90/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
