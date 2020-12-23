%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 8.26s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 438 expanded)
%              Number of leaves         :   41 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 (1732 expanded)
%              Number of equality atoms :   14 ( 115 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m2_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ? [C] : m2_subset_1(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
         => m1_subset_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_subset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_70,plain,(
    ! [A_60] :
      ( k1_struct_0(A_60) = k1_xboole_0
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_76,plain,(
    ! [A_63] :
      ( k1_struct_0(A_63) = k1_xboole_0
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_80,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_52,plain,(
    k3_orders_2('#skF_4',k1_struct_0('#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_86,plain,(
    k3_orders_2('#skF_4',k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_42,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1(k3_orders_2(A_36,B_37,C_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(C_38,u1_struct_0(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_510,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1(k3_orders_2(A_149,B_150,C_151),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_974,plain,(
    ! [A_213,B_214,C_215] :
      ( v1_xboole_0(k3_orders_2(A_213,B_214,C_215))
      | ~ v1_xboole_0(u1_struct_0(A_213))
      | ~ m1_subset_1(C_215,u1_struct_0(A_213))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_orders_2(A_213)
      | ~ v5_orders_2(A_213)
      | ~ v4_orders_2(A_213)
      | ~ v3_orders_2(A_213)
      | v2_struct_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_510,c_24])).

tff(c_994,plain,(
    ! [B_214] :
      ( v1_xboole_0(k3_orders_2('#skF_4',B_214,'#skF_5'))
      | ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_974])).

tff(c_1003,plain,(
    ! [B_214] :
      ( v1_xboole_0(k3_orders_2('#skF_4',B_214,'#skF_5'))
      | ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_994])).

tff(c_1004,plain,(
    ! [B_214] :
      ( v1_xboole_0(k3_orders_2('#skF_4',B_214,'#skF_5'))
      | ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1003])).

tff(c_1005,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1004])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_575,plain,(
    ! [B_163,D_164,A_165,C_166] :
      ( r2_hidden(B_163,D_164)
      | ~ r2_hidden(B_163,k3_orders_2(A_165,D_164,C_166))
      | ~ m1_subset_1(D_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(C_166,u1_struct_0(A_165))
      | ~ m1_subset_1(B_163,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1653,plain,(
    ! [A_291,D_292,A_293,C_294] :
      ( r2_hidden(A_291,D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ m1_subset_1(C_294,u1_struct_0(A_293))
      | ~ m1_subset_1(A_291,u1_struct_0(A_293))
      | ~ l1_orders_2(A_293)
      | ~ v5_orders_2(A_293)
      | ~ v4_orders_2(A_293)
      | ~ v3_orders_2(A_293)
      | v2_struct_0(A_293)
      | v1_xboole_0(k3_orders_2(A_293,D_292,C_294))
      | ~ m1_subset_1(A_291,k3_orders_2(A_293,D_292,C_294)) ) ),
    inference(resolution,[status(thm)],[c_26,c_575])).

tff(c_4781,plain,(
    ! [A_506,C_507,A_508] :
      ( r2_hidden(A_506,k1_xboole_0)
      | ~ m1_subset_1(C_507,u1_struct_0(A_508))
      | ~ m1_subset_1(A_506,u1_struct_0(A_508))
      | ~ l1_orders_2(A_508)
      | ~ v5_orders_2(A_508)
      | ~ v4_orders_2(A_508)
      | ~ v3_orders_2(A_508)
      | v2_struct_0(A_508)
      | v1_xboole_0(k3_orders_2(A_508,k1_xboole_0,C_507))
      | ~ m1_subset_1(A_506,k3_orders_2(A_508,k1_xboole_0,C_507)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1653])).

tff(c_4801,plain,(
    ! [A_506] :
      ( r2_hidden(A_506,k1_xboole_0)
      | ~ m1_subset_1(A_506,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))
      | ~ m1_subset_1(A_506,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_54,c_4781])).

tff(c_4810,plain,(
    ! [A_506] :
      ( r2_hidden(A_506,k1_xboole_0)
      | ~ m1_subset_1(A_506,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))
      | ~ m1_subset_1(A_506,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_4801])).

tff(c_4811,plain,(
    ! [A_506] :
      ( r2_hidden(A_506,k1_xboole_0)
      | ~ m1_subset_1(A_506,u1_struct_0('#skF_4'))
      | v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))
      | ~ m1_subset_1(A_506,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4810])).

tff(c_4812,plain,(
    v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4811])).

tff(c_141,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_118,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_167,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_156,c_123])).

tff(c_4829,plain,(
    k3_orders_2('#skF_4',k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4812,c_167])).

tff(c_4840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4829])).

tff(c_4842,plain,(
    ~ v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4811])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( m2_subset_1('#skF_3'(A_28,B_29),A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_478,plain,(
    ! [C_142,A_143,B_144] :
      ( m1_subset_1(C_142,A_143)
      | ~ m2_subset_1(C_142,A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143))
      | v1_xboole_0(B_144)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_481,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1('#skF_3'(A_28,B_29),A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_478])).

tff(c_366,plain,(
    ! [C_119,B_120,A_121] :
      ( m1_subset_1(C_119,B_120)
      | ~ m2_subset_1(C_119,A_121,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121))
      | v1_xboole_0(B_120)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_369,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1('#skF_3'(A_28,B_29),B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_366])).

tff(c_4843,plain,(
    ! [A_509] :
      ( r2_hidden(A_509,k1_xboole_0)
      | ~ m1_subset_1(A_509,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_509,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_4811])).

tff(c_4867,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'(A_28,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'),k1_zfmisc_1(A_28))
      | v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_369,c_4843])).

tff(c_4913,plain,(
    ! [A_516] :
      ( r2_hidden('#skF_3'(A_516,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'(A_516,k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'),k1_zfmisc_1(A_516))
      | v1_xboole_0(A_516) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4842,c_4867])).

tff(c_4917,plain,
    ( r2_hidden('#skF_3'(u1_struct_0('#skF_4'),k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),k1_xboole_0)
    | ~ m1_subset_1(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_481,c_4913])).

tff(c_4920,plain,
    ( r2_hidden('#skF_3'(u1_struct_0('#skF_4'),k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),k1_xboole_0)
    | ~ m1_subset_1(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_4842,c_1005,c_4917])).

tff(c_4921,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4920])).

tff(c_4924,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_4921])).

tff(c_4927,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_22,c_54,c_4924])).

tff(c_4929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4927])).

tff(c_4930,plain,(
    r2_hidden('#skF_3'(u1_struct_0('#skF_4'),k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4920])).

tff(c_30,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4969,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3'(u1_struct_0('#skF_4'),k3_orders_2('#skF_4',k1_xboole_0,'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4930,c_30])).

tff(c_4980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4969])).

tff(c_4982,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_4989,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4982,c_167])).

tff(c_4981,plain,(
    ! [B_214] :
      ( v1_xboole_0(k3_orders_2('#skF_4',B_214,'#skF_5'))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_5036,plain,(
    ! [B_521] :
      ( v1_xboole_0(k3_orders_2('#skF_4',B_521,'#skF_5'))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_4981])).

tff(c_5071,plain,(
    v1_xboole_0(k3_orders_2('#skF_4',k1_xboole_0,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_5036])).

tff(c_5105,plain,(
    k3_orders_2('#skF_4',k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5071,c_167])).

tff(c_5110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.26/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/2.92  
% 8.26/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/2.93  %$ r2_orders_2 > m2_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 8.26/2.93  
% 8.26/2.93  %Foreground sorts:
% 8.26/2.93  
% 8.26/2.93  
% 8.26/2.93  %Background operators:
% 8.26/2.93  
% 8.26/2.93  
% 8.26/2.93  %Foreground operators:
% 8.26/2.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.26/2.93  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.26/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.26/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.26/2.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.26/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.26/2.93  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 8.26/2.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.26/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.26/2.93  tff('#skF_5', type, '#skF_5': $i).
% 8.26/2.93  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.26/2.93  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.26/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.26/2.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.26/2.93  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.26/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.26/2.93  tff('#skF_4', type, '#skF_4': $i).
% 8.26/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.26/2.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.26/2.93  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 8.26/2.93  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 8.26/2.93  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 8.26/2.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.26/2.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.26/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.26/2.93  
% 8.26/2.94  tff(f_178, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 8.26/2.94  tff(f_135, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 8.26/2.94  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 8.26/2.94  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.26/2.94  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.26/2.94  tff(f_131, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 8.26/2.94  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.26/2.94  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.26/2.94  tff(f_161, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 8.26/2.94  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.26/2.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.26/2.94  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.26/2.94  tff(f_97, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (?[C]: m2_subset_1(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_subset_1)).
% 8.26/2.94  tff(f_86, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) => m1_subset_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_subset_1)).
% 8.26/2.94  tff(f_110, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 8.26/2.94  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.26/2.94  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_44, plain, (![A_39]: (l1_struct_0(A_39) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.26/2.94  tff(c_70, plain, (![A_60]: (k1_struct_0(A_60)=k1_xboole_0 | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.26/2.94  tff(c_76, plain, (![A_63]: (k1_struct_0(A_63)=k1_xboole_0 | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_44, c_70])).
% 8.26/2.94  tff(c_80, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_76])).
% 8.26/2.94  tff(c_52, plain, (k3_orders_2('#skF_4', k1_struct_0('#skF_4'), '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_86, plain, (k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52])).
% 8.26/2.94  tff(c_22, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.26/2.94  tff(c_20, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.26/2.94  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.26/2.94  tff(c_42, plain, (![A_36, B_37, C_38]: (m1_subset_1(k3_orders_2(A_36, B_37, C_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(C_38, u1_struct_0(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.26/2.94  tff(c_510, plain, (![A_149, B_150, C_151]: (m1_subset_1(k3_orders_2(A_149, B_150, C_151), k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.26/2.94  tff(c_24, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.26/2.94  tff(c_974, plain, (![A_213, B_214, C_215]: (v1_xboole_0(k3_orders_2(A_213, B_214, C_215)) | ~v1_xboole_0(u1_struct_0(A_213)) | ~m1_subset_1(C_215, u1_struct_0(A_213)) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_orders_2(A_213) | ~v5_orders_2(A_213) | ~v4_orders_2(A_213) | ~v3_orders_2(A_213) | v2_struct_0(A_213))), inference(resolution, [status(thm)], [c_510, c_24])).
% 8.26/2.94  tff(c_994, plain, (![B_214]: (v1_xboole_0(k3_orders_2('#skF_4', B_214, '#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_974])).
% 8.26/2.94  tff(c_1003, plain, (![B_214]: (v1_xboole_0(k3_orders_2('#skF_4', B_214, '#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_994])).
% 8.26/2.94  tff(c_1004, plain, (![B_214]: (v1_xboole_0(k3_orders_2('#skF_4', B_214, '#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1003])).
% 8.26/2.94  tff(c_1005, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1004])).
% 8.26/2.94  tff(c_26, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.26/2.94  tff(c_575, plain, (![B_163, D_164, A_165, C_166]: (r2_hidden(B_163, D_164) | ~r2_hidden(B_163, k3_orders_2(A_165, D_164, C_166)) | ~m1_subset_1(D_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(C_166, u1_struct_0(A_165)) | ~m1_subset_1(B_163, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.26/2.94  tff(c_1653, plain, (![A_291, D_292, A_293, C_294]: (r2_hidden(A_291, D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(u1_struct_0(A_293))) | ~m1_subset_1(C_294, u1_struct_0(A_293)) | ~m1_subset_1(A_291, u1_struct_0(A_293)) | ~l1_orders_2(A_293) | ~v5_orders_2(A_293) | ~v4_orders_2(A_293) | ~v3_orders_2(A_293) | v2_struct_0(A_293) | v1_xboole_0(k3_orders_2(A_293, D_292, C_294)) | ~m1_subset_1(A_291, k3_orders_2(A_293, D_292, C_294)))), inference(resolution, [status(thm)], [c_26, c_575])).
% 8.26/2.94  tff(c_4781, plain, (![A_506, C_507, A_508]: (r2_hidden(A_506, k1_xboole_0) | ~m1_subset_1(C_507, u1_struct_0(A_508)) | ~m1_subset_1(A_506, u1_struct_0(A_508)) | ~l1_orders_2(A_508) | ~v5_orders_2(A_508) | ~v4_orders_2(A_508) | ~v3_orders_2(A_508) | v2_struct_0(A_508) | v1_xboole_0(k3_orders_2(A_508, k1_xboole_0, C_507)) | ~m1_subset_1(A_506, k3_orders_2(A_508, k1_xboole_0, C_507)))), inference(resolution, [status(thm)], [c_22, c_1653])).
% 8.26/2.94  tff(c_4801, plain, (![A_506]: (r2_hidden(A_506, k1_xboole_0) | ~m1_subset_1(A_506, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')) | ~m1_subset_1(A_506, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')))), inference(resolution, [status(thm)], [c_54, c_4781])).
% 8.26/2.94  tff(c_4810, plain, (![A_506]: (r2_hidden(A_506, k1_xboole_0) | ~m1_subset_1(A_506, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')) | ~m1_subset_1(A_506, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_4801])).
% 8.26/2.94  tff(c_4811, plain, (![A_506]: (r2_hidden(A_506, k1_xboole_0) | ~m1_subset_1(A_506, u1_struct_0('#skF_4')) | v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')) | ~m1_subset_1(A_506, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_4810])).
% 8.26/2.94  tff(c_4812, plain, (v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'))), inference(splitLeft, [status(thm)], [c_4811])).
% 8.26/2.94  tff(c_141, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.26/2.94  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.26/2.94  tff(c_156, plain, (![A_77, B_78]: (~v1_xboole_0(A_77) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_141, c_2])).
% 8.26/2.94  tff(c_118, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/2.94  tff(c_123, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_118])).
% 8.26/2.94  tff(c_167, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_156, c_123])).
% 8.26/2.94  tff(c_4829, plain, (k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_4812, c_167])).
% 8.26/2.94  tff(c_4840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_4829])).
% 8.26/2.94  tff(c_4842, plain, (~v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'))), inference(splitRight, [status(thm)], [c_4811])).
% 8.26/2.94  tff(c_34, plain, (![A_28, B_29]: (m2_subset_1('#skF_3'(A_28, B_29), A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.26/2.94  tff(c_478, plain, (![C_142, A_143, B_144]: (m1_subset_1(C_142, A_143) | ~m2_subset_1(C_142, A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)) | v1_xboole_0(B_144) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.26/2.94  tff(c_481, plain, (![A_28, B_29]: (m1_subset_1('#skF_3'(A_28, B_29), A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_34, c_478])).
% 8.26/2.94  tff(c_366, plain, (![C_119, B_120, A_121]: (m1_subset_1(C_119, B_120) | ~m2_subset_1(C_119, A_121, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)) | v1_xboole_0(B_120) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.26/2.94  tff(c_369, plain, (![A_28, B_29]: (m1_subset_1('#skF_3'(A_28, B_29), B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_34, c_366])).
% 8.26/2.94  tff(c_4843, plain, (![A_509]: (r2_hidden(A_509, k1_xboole_0) | ~m1_subset_1(A_509, u1_struct_0('#skF_4')) | ~m1_subset_1(A_509, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')))), inference(splitRight, [status(thm)], [c_4811])).
% 8.26/2.94  tff(c_4867, plain, (![A_28]: (r2_hidden('#skF_3'(A_28, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), k1_xboole_0) | ~m1_subset_1('#skF_3'(A_28, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'), k1_zfmisc_1(A_28)) | v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')) | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_369, c_4843])).
% 8.26/2.94  tff(c_4913, plain, (![A_516]: (r2_hidden('#skF_3'(A_516, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), k1_xboole_0) | ~m1_subset_1('#skF_3'(A_516, k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'), k1_zfmisc_1(A_516)) | v1_xboole_0(A_516))), inference(negUnitSimplification, [status(thm)], [c_4842, c_4867])).
% 8.26/2.94  tff(c_4917, plain, (r2_hidden('#skF_3'(u1_struct_0('#skF_4'), k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), k1_xboole_0) | ~m1_subset_1(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_481, c_4913])).
% 8.26/2.94  tff(c_4920, plain, (r2_hidden('#skF_3'(u1_struct_0('#skF_4'), k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), k1_xboole_0) | ~m1_subset_1(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1005, c_4842, c_1005, c_4917])).
% 8.26/2.94  tff(c_4921, plain, (~m1_subset_1(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4920])).
% 8.26/2.94  tff(c_4924, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_4921])).
% 8.26/2.94  tff(c_4927, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_22, c_54, c_4924])).
% 8.26/2.94  tff(c_4929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4927])).
% 8.26/2.94  tff(c_4930, plain, (r2_hidden('#skF_3'(u1_struct_0('#skF_4'), k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_4920])).
% 8.26/2.94  tff(c_30, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.26/2.94  tff(c_4969, plain, (~r1_tarski(k1_xboole_0, '#skF_3'(u1_struct_0('#skF_4'), k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')))), inference(resolution, [status(thm)], [c_4930, c_30])).
% 8.26/2.94  tff(c_4980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_4969])).
% 8.26/2.94  tff(c_4982, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1004])).
% 8.26/2.94  tff(c_4989, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4982, c_167])).
% 8.26/2.94  tff(c_4981, plain, (![B_214]: (v1_xboole_0(k3_orders_2('#skF_4', B_214, '#skF_5')) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1004])).
% 8.26/2.94  tff(c_5036, plain, (![B_521]: (v1_xboole_0(k3_orders_2('#skF_4', B_521, '#skF_5')) | ~m1_subset_1(B_521, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4989, c_4981])).
% 8.26/2.94  tff(c_5071, plain, (v1_xboole_0(k3_orders_2('#skF_4', k1_xboole_0, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_5036])).
% 8.26/2.94  tff(c_5105, plain, (k3_orders_2('#skF_4', k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5071, c_167])).
% 8.26/2.94  tff(c_5110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_5105])).
% 8.26/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/2.94  
% 8.26/2.94  Inference rules
% 8.26/2.94  ----------------------
% 8.26/2.94  #Ref     : 0
% 8.26/2.94  #Sup     : 1119
% 8.26/2.94  #Fact    : 0
% 8.26/2.94  #Define  : 0
% 8.26/2.94  #Split   : 4
% 8.26/2.94  #Chain   : 0
% 8.26/2.94  #Close   : 0
% 8.26/2.94  
% 8.26/2.94  Ordering : KBO
% 8.26/2.94  
% 8.26/2.94  Simplification rules
% 8.26/2.94  ----------------------
% 8.26/2.94  #Subsume      : 282
% 8.26/2.94  #Demod        : 128
% 8.26/2.94  #Tautology    : 128
% 8.26/2.94  #SimpNegUnit  : 17
% 8.26/2.94  #BackRed      : 2
% 8.26/2.94  
% 8.26/2.94  #Partial instantiations: 0
% 8.26/2.94  #Strategies tried      : 1
% 8.26/2.94  
% 8.26/2.94  Timing (in seconds)
% 8.26/2.94  ----------------------
% 8.26/2.95  Preprocessing        : 0.34
% 8.26/2.95  Parsing              : 0.19
% 8.26/2.95  CNF conversion       : 0.03
% 8.26/2.95  Main loop            : 1.83
% 8.26/2.95  Inferencing          : 0.43
% 8.26/2.95  Reduction            : 0.34
% 8.26/2.95  Demodulation         : 0.23
% 8.26/2.95  BG Simplification    : 0.05
% 8.26/2.95  Subsumption          : 0.91
% 8.26/2.95  Abstraction          : 0.07
% 8.26/2.95  MUC search           : 0.00
% 8.26/2.95  Cooper               : 0.00
% 8.26/2.95  Total                : 2.21
% 8.26/2.95  Index Insertion      : 0.00
% 8.26/2.95  Index Deletion       : 0.00
% 8.26/2.95  Index Matching       : 0.00
% 8.26/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
