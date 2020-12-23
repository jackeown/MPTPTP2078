%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 181 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 ( 528 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3766,plain,(
    ! [B_307,A_308] :
      ( l1_pre_topc(B_307)
      | ~ m1_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3769,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3766])).

tff(c_3778,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3769])).

tff(c_36,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3772,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_3766])).

tff(c_3781,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3772])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_75,plain,(
    ! [B_41,A_42] :
      ( l1_pre_topc(B_41)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_75])).

tff(c_87,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_78])).

tff(c_50,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_68,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_133,plain,(
    ! [B_73,A_74] :
      ( r1_tsep_1(B_73,A_74)
      | ~ r1_tsep_1(A_74,B_73)
      | ~ l1_struct_0(B_73)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_136,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_133])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_140,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_140])).

tff(c_146,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_90,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_81])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_145,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_147])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_155])).

tff(c_161,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_160,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [B_77,A_78] :
      ( m1_subset_1(u1_struct_0(B_77),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_172,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(u1_struct_0(B_79),u1_struct_0(A_80))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_167,c_32])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_220,plain,(
    ! [B_92,A_93] :
      ( k2_xboole_0(u1_struct_0(B_92),u1_struct_0(A_93)) = u1_struct_0(A_93)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_172,c_30])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_243,plain,(
    ! [D_97,B_98,A_99] :
      ( ~ r2_hidden(D_97,u1_struct_0(B_98))
      | r2_hidden(D_97,u1_struct_0(A_99))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_10])).

tff(c_255,plain,(
    ! [B_98,A_99] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_98)),u1_struct_0(A_99))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99)
      | v1_xboole_0(u1_struct_0(B_98)) ) ),
    inference(resolution,[status(thm)],[c_4,c_243])).

tff(c_212,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(u1_struct_0(A_90),u1_struct_0(B_91))
      | ~ r1_tsep_1(A_90,B_91)
      | ~ l1_struct_0(B_91)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_274,plain,(
    ! [C_107,B_108,A_109] :
      ( ~ r2_hidden(C_107,u1_struct_0(B_108))
      | ~ r2_hidden(C_107,u1_struct_0(A_109))
      | ~ r1_tsep_1(A_109,B_108)
      | ~ l1_struct_0(B_108)
      | ~ l1_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_212,c_24])).

tff(c_3250,plain,(
    ! [B_276,A_277] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0(B_276)),u1_struct_0(A_277))
      | ~ r1_tsep_1(A_277,B_276)
      | ~ l1_struct_0(B_276)
      | ~ l1_struct_0(A_277)
      | v1_xboole_0(u1_struct_0(B_276)) ) ),
    inference(resolution,[status(thm)],[c_4,c_274])).

tff(c_3680,plain,(
    ! [A_296,B_297] :
      ( ~ r1_tsep_1(A_296,B_297)
      | ~ l1_struct_0(B_297)
      | ~ l1_struct_0(A_296)
      | ~ m1_pre_topc(B_297,A_296)
      | ~ l1_pre_topc(A_296)
      | v1_xboole_0(u1_struct_0(B_297)) ) ),
    inference(resolution,[status(thm)],[c_255,c_3250])).

tff(c_3682,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_160,c_3680])).

tff(c_3687,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_52,c_161,c_146,c_3682])).

tff(c_40,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3721,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3687,c_40])).

tff(c_3748,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3721])).

tff(c_3750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3748])).

tff(c_3752,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3751,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3817,plain,(
    ! [B_333,A_334] :
      ( r1_tsep_1(B_333,A_334)
      | ~ r1_tsep_1(A_334,B_333)
      | ~ l1_struct_0(B_333)
      | ~ l1_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3819,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3751,c_3817])).

tff(c_3822,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3752,c_3819])).

tff(c_3823,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3822])).

tff(c_3826,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_3823])).

tff(c_3830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3781,c_3826])).

tff(c_3831,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3822])).

tff(c_3835,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_3831])).

tff(c_3839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3778,c_3835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:28:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.16  
% 6.09/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.17  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.09/2.17  
% 6.09/2.17  %Foreground sorts:
% 6.09/2.17  
% 6.09/2.17  
% 6.09/2.17  %Background operators:
% 6.09/2.17  
% 6.09/2.17  
% 6.09/2.17  %Foreground operators:
% 6.09/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.09/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.09/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.09/2.17  tff('#skF_7', type, '#skF_7': $i).
% 6.09/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.17  tff('#skF_5', type, '#skF_5': $i).
% 6.09/2.17  tff('#skF_6', type, '#skF_6': $i).
% 6.09/2.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.09/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.09/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.09/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.09/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.09/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.09/2.17  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.09/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.09/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.09/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.09/2.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.09/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.17  
% 6.31/2.18  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 6.31/2.18  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.31/2.18  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.31/2.18  tff(f_102, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 6.31/2.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.31/2.18  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.31/2.18  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.31/2.18  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.31/2.18  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.31/2.18  tff(f_94, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 6.31/2.18  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.31/2.18  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.31/2.18  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_58, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_3766, plain, (![B_307, A_308]: (l1_pre_topc(B_307) | ~m1_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.31/2.18  tff(c_3769, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_3766])).
% 6.31/2.18  tff(c_3778, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3769])).
% 6.31/2.18  tff(c_36, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.31/2.18  tff(c_54, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_3772, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_3766])).
% 6.31/2.18  tff(c_3781, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3772])).
% 6.31/2.18  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_75, plain, (![B_41, A_42]: (l1_pre_topc(B_41) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.31/2.18  tff(c_78, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_75])).
% 6.31/2.18  tff(c_87, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_78])).
% 6.31/2.18  tff(c_50, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_68, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 6.31/2.18  tff(c_133, plain, (![B_73, A_74]: (r1_tsep_1(B_73, A_74) | ~r1_tsep_1(A_74, B_73) | ~l1_struct_0(B_73) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.31/2.18  tff(c_136, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_133])).
% 6.31/2.18  tff(c_137, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_136])).
% 6.31/2.18  tff(c_140, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_137])).
% 6.31/2.18  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_140])).
% 6.31/2.18  tff(c_146, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 6.31/2.18  tff(c_81, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_75])).
% 6.31/2.18  tff(c_90, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_81])).
% 6.31/2.18  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.31/2.18  tff(c_145, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 6.31/2.18  tff(c_147, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_145])).
% 6.31/2.18  tff(c_155, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_147])).
% 6.31/2.18  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_155])).
% 6.31/2.18  tff(c_161, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_145])).
% 6.31/2.18  tff(c_160, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_145])).
% 6.31/2.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.31/2.18  tff(c_167, plain, (![B_77, A_78]: (m1_subset_1(u1_struct_0(B_77), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.31/2.18  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.18  tff(c_172, plain, (![B_79, A_80]: (r1_tarski(u1_struct_0(B_79), u1_struct_0(A_80)) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_167, c_32])).
% 6.31/2.18  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.31/2.18  tff(c_220, plain, (![B_92, A_93]: (k2_xboole_0(u1_struct_0(B_92), u1_struct_0(A_93))=u1_struct_0(A_93) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_172, c_30])).
% 6.31/2.18  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.31/2.18  tff(c_243, plain, (![D_97, B_98, A_99]: (~r2_hidden(D_97, u1_struct_0(B_98)) | r2_hidden(D_97, u1_struct_0(A_99)) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(superposition, [status(thm), theory('equality')], [c_220, c_10])).
% 6.31/2.18  tff(c_255, plain, (![B_98, A_99]: (r2_hidden('#skF_1'(u1_struct_0(B_98)), u1_struct_0(A_99)) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99) | v1_xboole_0(u1_struct_0(B_98)))), inference(resolution, [status(thm)], [c_4, c_243])).
% 6.31/2.18  tff(c_212, plain, (![A_90, B_91]: (r1_xboole_0(u1_struct_0(A_90), u1_struct_0(B_91)) | ~r1_tsep_1(A_90, B_91) | ~l1_struct_0(B_91) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.31/2.18  tff(c_24, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.31/2.18  tff(c_274, plain, (![C_107, B_108, A_109]: (~r2_hidden(C_107, u1_struct_0(B_108)) | ~r2_hidden(C_107, u1_struct_0(A_109)) | ~r1_tsep_1(A_109, B_108) | ~l1_struct_0(B_108) | ~l1_struct_0(A_109))), inference(resolution, [status(thm)], [c_212, c_24])).
% 6.31/2.18  tff(c_3250, plain, (![B_276, A_277]: (~r2_hidden('#skF_1'(u1_struct_0(B_276)), u1_struct_0(A_277)) | ~r1_tsep_1(A_277, B_276) | ~l1_struct_0(B_276) | ~l1_struct_0(A_277) | v1_xboole_0(u1_struct_0(B_276)))), inference(resolution, [status(thm)], [c_4, c_274])).
% 6.31/2.18  tff(c_3680, plain, (![A_296, B_297]: (~r1_tsep_1(A_296, B_297) | ~l1_struct_0(B_297) | ~l1_struct_0(A_296) | ~m1_pre_topc(B_297, A_296) | ~l1_pre_topc(A_296) | v1_xboole_0(u1_struct_0(B_297)))), inference(resolution, [status(thm)], [c_255, c_3250])).
% 6.31/2.18  tff(c_3682, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_160, c_3680])).
% 6.31/2.18  tff(c_3687, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_52, c_161, c_146, c_3682])).
% 6.31/2.18  tff(c_40, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.31/2.18  tff(c_3721, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_3687, c_40])).
% 6.31/2.18  tff(c_3748, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3721])).
% 6.31/2.18  tff(c_3750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3748])).
% 6.31/2.18  tff(c_3752, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 6.31/2.18  tff(c_3751, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 6.31/2.18  tff(c_3817, plain, (![B_333, A_334]: (r1_tsep_1(B_333, A_334) | ~r1_tsep_1(A_334, B_333) | ~l1_struct_0(B_333) | ~l1_struct_0(A_334))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.31/2.18  tff(c_3819, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3751, c_3817])).
% 6.31/2.18  tff(c_3822, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3752, c_3819])).
% 6.31/2.18  tff(c_3823, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3822])).
% 6.31/2.18  tff(c_3826, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_3823])).
% 6.31/2.18  tff(c_3830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3781, c_3826])).
% 6.31/2.18  tff(c_3831, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_3822])).
% 6.31/2.18  tff(c_3835, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_3831])).
% 6.31/2.18  tff(c_3839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3778, c_3835])).
% 6.31/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.18  
% 6.31/2.18  Inference rules
% 6.31/2.18  ----------------------
% 6.31/2.18  #Ref     : 0
% 6.31/2.18  #Sup     : 951
% 6.31/2.18  #Fact    : 8
% 6.31/2.18  #Define  : 0
% 6.31/2.18  #Split   : 6
% 6.31/2.18  #Chain   : 0
% 6.31/2.18  #Close   : 0
% 6.31/2.18  
% 6.31/2.18  Ordering : KBO
% 6.31/2.18  
% 6.31/2.18  Simplification rules
% 6.31/2.18  ----------------------
% 6.31/2.18  #Subsume      : 454
% 6.31/2.18  #Demod        : 114
% 6.31/2.18  #Tautology    : 148
% 6.31/2.18  #SimpNegUnit  : 2
% 6.31/2.18  #BackRed      : 12
% 6.31/2.18  
% 6.31/2.18  #Partial instantiations: 0
% 6.31/2.18  #Strategies tried      : 1
% 6.31/2.18  
% 6.31/2.18  Timing (in seconds)
% 6.31/2.18  ----------------------
% 6.31/2.19  Preprocessing        : 0.33
% 6.31/2.19  Parsing              : 0.18
% 6.31/2.19  CNF conversion       : 0.03
% 6.31/2.19  Main loop            : 1.09
% 6.31/2.19  Inferencing          : 0.34
% 6.31/2.19  Reduction            : 0.22
% 6.31/2.19  Demodulation         : 0.15
% 6.31/2.19  BG Simplification    : 0.04
% 6.31/2.19  Subsumption          : 0.41
% 6.31/2.19  Abstraction          : 0.05
% 6.31/2.19  MUC search           : 0.00
% 6.31/2.19  Cooper               : 0.00
% 6.31/2.19  Total                : 1.45
% 6.31/2.19  Index Insertion      : 0.00
% 6.31/2.19  Index Deletion       : 0.00
% 6.31/2.19  Index Matching       : 0.00
% 6.31/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
