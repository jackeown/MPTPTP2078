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
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 283 expanded)
%              Number of leaves         :   48 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 819 expanded)
%              Number of equality atoms :   34 ( 109 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_34,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_71,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | A_30 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_40,plain,(
    ! [A_54] :
      ( v4_pre_topc(k2_struct_0(A_54),A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    ! [A_53] :
      ( l1_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_114,plain,(
    ! [A_77] :
      ( u1_struct_0(A_77) = k2_struct_0(A_77)
      | ~ l1_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_125,plain,(
    ! [A_81] :
      ( u1_struct_0(A_81) = k2_struct_0(A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_129,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_130,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_56])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_211,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ v1_xboole_0(C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_216,plain,(
    ! [A_12,A_97] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_211])).

tff(c_219,plain,(
    ! [A_97] : ~ r2_hidden(A_97,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_5') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_79,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_6])).

tff(c_173,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_182,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_5') = k4_xboole_0(A_3,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_173])).

tff(c_185,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_5') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_182])).

tff(c_239,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_242,plain,(
    ! [A_12] : k4_xboole_0(A_12,'#skF_5') = k3_subset_1(A_12,'#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_239])).

tff(c_247,plain,(
    ! [A_12] : k3_subset_1(A_12,'#skF_5') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_242])).

tff(c_22,plain,(
    ! [C_19,A_13,B_17] :
      ( r2_hidden(C_19,k3_subset_1(A_13,B_17))
      | r2_hidden(C_19,B_17)
      | ~ m1_subset_1(C_19,A_13)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_13))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_391,plain,(
    ! [C_121,A_122,B_123] :
      ( r2_hidden(C_121,k3_subset_1(A_122,B_123))
      | r2_hidden(C_121,B_123)
      | ~ m1_subset_1(C_121,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122))
      | A_122 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_22])).

tff(c_403,plain,(
    ! [C_121,A_12] :
      ( r2_hidden(C_121,A_12)
      | r2_hidden(C_121,'#skF_5')
      | ~ m1_subset_1(C_121,A_12)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_12))
      | A_12 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_391])).

tff(c_408,plain,(
    ! [C_121,A_12] :
      ( r2_hidden(C_121,A_12)
      | r2_hidden(C_121,'#skF_5')
      | ~ m1_subset_1(C_121,A_12)
      | A_12 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_403])).

tff(c_409,plain,(
    ! [C_121,A_12] :
      ( r2_hidden(C_121,A_12)
      | ~ m1_subset_1(C_121,A_12)
      | A_12 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_408])).

tff(c_42,plain,(
    ! [A_55] :
      ( v3_pre_topc(k2_struct_0(A_55),A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_64,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_5')
      | ~ r2_hidden('#skF_4',D_69)
      | ~ v4_pre_topc(D_69,'#skF_3')
      | ~ v3_pre_topc(D_69,'#skF_3')
      | ~ m1_subset_1(D_69,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_310,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_5')
      | ~ r2_hidden('#skF_4',D_69)
      | ~ v4_pre_topc(D_69,'#skF_3')
      | ~ v3_pre_topc(D_69,'#skF_3')
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_64])).

tff(c_312,plain,(
    ! [D_116] :
      ( ~ r2_hidden('#skF_4',D_116)
      | ~ v4_pre_topc(D_116,'#skF_3')
      | ~ v3_pre_topc(D_116,'#skF_3')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_310])).

tff(c_327,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_312])).

tff(c_507,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_510,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_507])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_510])).

tff(c_515,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_528,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_542,plain,
    ( ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_409,c_528])).

tff(c_545,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_542])).

tff(c_359,plain,(
    ! [A_120] :
      ( m1_subset_1('#skF_2'(A_120),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_369,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_359])).

tff(c_374,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_369])).

tff(c_375,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_374])).

tff(c_28,plain,(
    ! [C_27,B_26,A_25] :
      ( ~ v1_xboole_0(C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_389,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_25,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_375,c_28])).

tff(c_390,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_552,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_390])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_552])).

tff(c_560,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_564,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_560])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_564])).

tff(c_631,plain,(
    ! [A_142] : ~ r2_hidden(A_142,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_636,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71,c_631])).

tff(c_48,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0('#skF_2'(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_650,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_48])).

tff(c_663,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_80,c_650])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_663])).

tff(c_666,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:10:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.88/1.41  
% 2.88/1.41  %Foreground sorts:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Background operators:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Foreground operators:
% 2.88/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.88/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.88/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.88/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.88/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.88/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.88/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.88/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.88/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.88/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.88/1.41  
% 2.88/1.43  tff(f_166, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.88/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.88/1.43  tff(f_101, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.88/1.43  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.88/1.43  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.88/1.43  tff(f_105, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.88/1.43  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.88/1.43  tff(f_75, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.88/1.43  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.88/1.43  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.88/1.43  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.88/1.43  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.88/1.43  tff(f_60, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.88/1.43  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.88/1.43  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.88/1.43  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.88/1.43  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.88/1.43  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_52, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.88/1.43  tff(c_80, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 2.88/1.43  tff(c_34, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.43  tff(c_71, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | A_30='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34])).
% 2.88/1.43  tff(c_40, plain, (![A_54]: (v4_pre_topc(k2_struct_0(A_54), A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.88/1.43  tff(c_38, plain, (![A_53]: (l1_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.88/1.43  tff(c_114, plain, (![A_77]: (u1_struct_0(A_77)=k2_struct_0(A_77) | ~l1_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.88/1.43  tff(c_125, plain, (![A_81]: (u1_struct_0(A_81)=k2_struct_0(A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_38, c_114])).
% 2.88/1.43  tff(c_129, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_125])).
% 2.88/1.43  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_130, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_56])).
% 2.88/1.43  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.43  tff(c_74, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 2.88/1.43  tff(c_211, plain, (![C_95, B_96, A_97]: (~v1_xboole_0(C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.43  tff(c_216, plain, (![A_12, A_97]: (~v1_xboole_0(A_12) | ~r2_hidden(A_97, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_211])).
% 2.88/1.43  tff(c_219, plain, (![A_97]: (~r2_hidden(A_97, '#skF_5'))), inference(splitLeft, [status(thm)], [c_216])).
% 2.88/1.43  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.88/1.43  tff(c_77, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_5')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 2.88/1.43  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.88/1.43  tff(c_79, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_6])).
% 2.88/1.43  tff(c_173, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.88/1.43  tff(c_182, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_5')=k4_xboole_0(A_3, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_173])).
% 2.88/1.43  tff(c_185, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_5')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_182])).
% 2.88/1.43  tff(c_239, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.43  tff(c_242, plain, (![A_12]: (k4_xboole_0(A_12, '#skF_5')=k3_subset_1(A_12, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_239])).
% 2.88/1.43  tff(c_247, plain, (![A_12]: (k3_subset_1(A_12, '#skF_5')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_242])).
% 2.88/1.43  tff(c_22, plain, (![C_19, A_13, B_17]: (r2_hidden(C_19, k3_subset_1(A_13, B_17)) | r2_hidden(C_19, B_17) | ~m1_subset_1(C_19, A_13) | ~m1_subset_1(B_17, k1_zfmisc_1(A_13)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.43  tff(c_391, plain, (![C_121, A_122, B_123]: (r2_hidden(C_121, k3_subset_1(A_122, B_123)) | r2_hidden(C_121, B_123) | ~m1_subset_1(C_121, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)) | A_122='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_22])).
% 2.88/1.43  tff(c_403, plain, (![C_121, A_12]: (r2_hidden(C_121, A_12) | r2_hidden(C_121, '#skF_5') | ~m1_subset_1(C_121, A_12) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_12)) | A_12='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_247, c_391])).
% 2.88/1.43  tff(c_408, plain, (![C_121, A_12]: (r2_hidden(C_121, A_12) | r2_hidden(C_121, '#skF_5') | ~m1_subset_1(C_121, A_12) | A_12='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_403])).
% 2.88/1.43  tff(c_409, plain, (![C_121, A_12]: (r2_hidden(C_121, A_12) | ~m1_subset_1(C_121, A_12) | A_12='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_219, c_408])).
% 2.88/1.43  tff(c_42, plain, (![A_55]: (v3_pre_topc(k2_struct_0(A_55), A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.88/1.43  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.43  tff(c_18, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.43  tff(c_76, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 2.88/1.43  tff(c_64, plain, (![D_69]: (r2_hidden(D_69, '#skF_5') | ~r2_hidden('#skF_4', D_69) | ~v4_pre_topc(D_69, '#skF_3') | ~v3_pre_topc(D_69, '#skF_3') | ~m1_subset_1(D_69, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.88/1.43  tff(c_310, plain, (![D_69]: (r2_hidden(D_69, '#skF_5') | ~r2_hidden('#skF_4', D_69) | ~v4_pre_topc(D_69, '#skF_3') | ~v3_pre_topc(D_69, '#skF_3') | ~m1_subset_1(D_69, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_64])).
% 2.88/1.43  tff(c_312, plain, (![D_116]: (~r2_hidden('#skF_4', D_116) | ~v4_pre_topc(D_116, '#skF_3') | ~v3_pre_topc(D_116, '#skF_3') | ~m1_subset_1(D_116, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_219, c_310])).
% 2.88/1.43  tff(c_327, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_76, c_312])).
% 2.88/1.43  tff(c_507, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_327])).
% 2.88/1.43  tff(c_510, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_507])).
% 2.88/1.43  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_510])).
% 2.88/1.43  tff(c_515, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_327])).
% 2.88/1.43  tff(c_528, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_515])).
% 2.88/1.43  tff(c_542, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_409, c_528])).
% 2.88/1.43  tff(c_545, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_542])).
% 2.88/1.43  tff(c_359, plain, (![A_120]: (m1_subset_1('#skF_2'(A_120), k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.88/1.43  tff(c_369, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_359])).
% 2.88/1.43  tff(c_374, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_369])).
% 2.88/1.43  tff(c_375, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_374])).
% 2.88/1.43  tff(c_28, plain, (![C_27, B_26, A_25]: (~v1_xboole_0(C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(C_27)) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.43  tff(c_389, plain, (![A_25]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_25, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_375, c_28])).
% 2.88/1.43  tff(c_390, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_389])).
% 2.88/1.43  tff(c_552, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_390])).
% 2.88/1.43  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_552])).
% 2.88/1.43  tff(c_560, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_515])).
% 2.88/1.43  tff(c_564, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_560])).
% 2.88/1.43  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_564])).
% 2.88/1.43  tff(c_631, plain, (![A_142]: (~r2_hidden(A_142, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_389])).
% 2.88/1.43  tff(c_636, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_71, c_631])).
% 2.88/1.43  tff(c_48, plain, (![A_56]: (~v1_xboole_0('#skF_2'(A_56)) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.88/1.43  tff(c_650, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_636, c_48])).
% 2.88/1.43  tff(c_663, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_80, c_650])).
% 2.88/1.43  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_663])).
% 2.88/1.43  tff(c_666, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_216])).
% 2.88/1.43  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_80])).
% 2.88/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  Inference rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Ref     : 0
% 2.88/1.43  #Sup     : 118
% 2.88/1.43  #Fact    : 0
% 2.88/1.43  #Define  : 0
% 2.88/1.43  #Split   : 8
% 2.88/1.43  #Chain   : 0
% 2.88/1.43  #Close   : 0
% 2.88/1.43  
% 2.88/1.43  Ordering : KBO
% 2.88/1.43  
% 2.88/1.43  Simplification rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Subsume      : 21
% 2.88/1.43  #Demod        : 85
% 2.88/1.43  #Tautology    : 48
% 2.88/1.43  #SimpNegUnit  : 16
% 2.88/1.43  #BackRed      : 22
% 2.88/1.43  
% 2.88/1.43  #Partial instantiations: 0
% 2.88/1.43  #Strategies tried      : 1
% 2.88/1.43  
% 2.88/1.43  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.43  Preprocessing        : 0.35
% 2.88/1.43  Parsing              : 0.19
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.32
% 2.88/1.43  Inferencing          : 0.11
% 2.88/1.43  Reduction            : 0.10
% 2.88/1.43  Demodulation         : 0.07
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.05
% 2.88/1.43  Abstraction          : 0.01
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.71
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
