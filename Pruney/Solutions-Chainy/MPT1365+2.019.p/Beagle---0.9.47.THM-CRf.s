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
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 193 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 585 expanded)
%              Number of equality atoms :    7 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_107,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_3') = k3_xboole_0(B_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_120,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_24])).

tff(c_41,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_140,plain,(
    ! [B_51,A_52] :
      ( v4_pre_topc(B_51,A_52)
      | ~ v2_compts_1(B_51,A_52)
      | ~ v8_pre_topc(A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_159,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_26,c_151])).

tff(c_28,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_154,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_140])).

tff(c_162,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_154])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_241,plain,(
    ! [B_61,C_62,A_63] :
      ( v4_pre_topc(k3_xboole_0(B_61,C_62),A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v4_pre_topc(C_62,A_63)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v4_pre_topc(B_61,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_684,plain,(
    ! [B_114,A_115,A_116] :
      ( v4_pre_topc(k3_xboole_0(B_114,A_115),A_116)
      | ~ v4_pre_topc(A_115,A_116)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v4_pre_topc(B_114,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ r1_tarski(A_115,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_16,c_241])).

tff(c_705,plain,(
    ! [A_115] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_115),'#skF_1')
      | ~ v4_pre_topc(A_115,'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_115,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_684])).

tff(c_726,plain,(
    ! [A_115] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_115),'#skF_1')
      | ~ v4_pre_topc(A_115,'#skF_1')
      | ~ r1_tarski(A_115,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_162,c_705])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [B_50] :
      ( m1_subset_1(k3_xboole_0(B_50,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_10])).

tff(c_138,plain,(
    ! [B_50] : m1_subset_1(k3_xboole_0(B_50,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_220,plain,(
    ! [B_58,B_59,A_60] :
      ( k9_subset_1(B_58,B_59,A_60) = k3_xboole_0(B_59,A_60)
      | ~ r1_tarski(A_60,B_58) ) ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_240,plain,(
    ! [B_2,B_59] : k9_subset_1(B_2,B_59,B_2) = k3_xboole_0(B_59,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_83,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k9_subset_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(k9_subset_1(A_39,B_40,C_41),A_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_348,plain,(
    ! [C_74,A_75,B_76] :
      ( v2_compts_1(C_74,A_75)
      | ~ v4_pre_topc(C_74,A_75)
      | ~ r1_tarski(C_74,B_76)
      | ~ v2_compts_1(B_76,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2243,plain,(
    ! [A_296,B_297,C_298,A_299] :
      ( v2_compts_1(k9_subset_1(A_296,B_297,C_298),A_299)
      | ~ v4_pre_topc(k9_subset_1(A_296,B_297,C_298),A_299)
      | ~ v2_compts_1(A_296,A_299)
      | ~ m1_subset_1(k9_subset_1(A_296,B_297,C_298),k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_subset_1(A_296,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(A_296)) ) ),
    inference(resolution,[status(thm)],[c_87,c_348])).

tff(c_2279,plain,(
    ! [B_2,B_59,A_299] :
      ( v2_compts_1(k9_subset_1(B_2,B_59,B_2),A_299)
      | ~ v4_pre_topc(k9_subset_1(B_2,B_59,B_2),A_299)
      | ~ v2_compts_1(B_2,A_299)
      | ~ m1_subset_1(k3_xboole_0(B_59,B_2),k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2243])).

tff(c_5205,plain,(
    ! [B_640,B_641,A_642] :
      ( v2_compts_1(k3_xboole_0(B_640,B_641),A_642)
      | ~ v4_pre_topc(k3_xboole_0(B_640,B_641),A_642)
      | ~ v2_compts_1(B_641,A_642)
      | ~ m1_subset_1(k3_xboole_0(B_640,B_641),k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(B_641)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_240,c_2279])).

tff(c_5260,plain,(
    ! [B_50] :
      ( v2_compts_1(k3_xboole_0(B_50,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_50,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_138,c_5205])).

tff(c_5314,plain,(
    ! [B_50] :
      ( v2_compts_1(k3_xboole_0(B_50,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_50,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_26,c_5260])).

tff(c_5579,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5314])).

tff(c_5582,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_5579])).

tff(c_5586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5582])).

tff(c_5838,plain,(
    ! [B_668] :
      ( v2_compts_1(k3_xboole_0(B_668,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_668,'#skF_3'),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_5314])).

tff(c_5917,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_726,c_5838])).

tff(c_5982,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_159,c_5917])).

tff(c_5984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_5982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:35:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.89  
% 7.80/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.89  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.80/2.89  
% 7.80/2.89  %Foreground sorts:
% 7.80/2.89  
% 7.80/2.89  
% 7.80/2.89  %Background operators:
% 7.80/2.89  
% 7.80/2.89  
% 7.80/2.89  %Foreground operators:
% 7.80/2.89  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 7.80/2.89  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 7.80/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.80/2.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.80/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.80/2.89  tff('#skF_2', type, '#skF_2': $i).
% 7.80/2.89  tff('#skF_3', type, '#skF_3': $i).
% 7.80/2.89  tff('#skF_1', type, '#skF_1': $i).
% 7.80/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.80/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.80/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.80/2.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.80/2.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.80/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.89  
% 7.80/2.91  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 7.80/2.91  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.80/2.91  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.80/2.91  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 7.80/2.91  tff(f_59, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 7.80/2.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.80/2.91  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.80/2.91  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 7.80/2.91  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_107, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, C_49)=k3_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/2.91  tff(c_118, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_3')=k3_xboole_0(B_48, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_107])).
% 7.80/2.91  tff(c_24, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_120, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_24])).
% 7.80/2.91  tff(c_41, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.91  tff(c_48, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_41])).
% 7.80/2.91  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_30, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_26, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_140, plain, (![B_51, A_52]: (v4_pre_topc(B_51, A_52) | ~v2_compts_1(B_51, A_52) | ~v8_pre_topc(A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.80/2.91  tff(c_151, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_140])).
% 7.80/2.91  tff(c_159, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_26, c_151])).
% 7.80/2.91  tff(c_28, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.80/2.91  tff(c_154, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_140])).
% 7.80/2.91  tff(c_162, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_154])).
% 7.80/2.91  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.91  tff(c_241, plain, (![B_61, C_62, A_63]: (v4_pre_topc(k3_xboole_0(B_61, C_62), A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~v4_pre_topc(C_62, A_63) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_63))) | ~v4_pre_topc(B_61, A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.91  tff(c_684, plain, (![B_114, A_115, A_116]: (v4_pre_topc(k3_xboole_0(B_114, A_115), A_116) | ~v4_pre_topc(A_115, A_116) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_116))) | ~v4_pre_topc(B_114, A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~r1_tarski(A_115, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_16, c_241])).
% 7.80/2.91  tff(c_705, plain, (![A_115]: (v4_pre_topc(k3_xboole_0('#skF_2', A_115), '#skF_1') | ~v4_pre_topc(A_115, '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_115, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_684])).
% 7.80/2.91  tff(c_726, plain, (![A_115]: (v4_pre_topc(k3_xboole_0('#skF_2', A_115), '#skF_1') | ~v4_pre_topc(A_115, '#skF_1') | ~r1_tarski(A_115, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_162, c_705])).
% 7.80/2.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/2.91  tff(c_121, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_107])).
% 7.80/2.91  tff(c_10, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/2.91  tff(c_130, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_121, c_10])).
% 7.80/2.91  tff(c_138, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130])).
% 7.80/2.91  tff(c_220, plain, (![B_58, B_59, A_60]: (k9_subset_1(B_58, B_59, A_60)=k3_xboole_0(B_59, A_60) | ~r1_tarski(A_60, B_58))), inference(resolution, [status(thm)], [c_16, c_107])).
% 7.80/2.91  tff(c_240, plain, (![B_2, B_59]: (k9_subset_1(B_2, B_59, B_2)=k3_xboole_0(B_59, B_2))), inference(resolution, [status(thm)], [c_6, c_220])).
% 7.80/2.91  tff(c_83, plain, (![A_39, B_40, C_41]: (m1_subset_1(k9_subset_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/2.91  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.91  tff(c_87, plain, (![A_39, B_40, C_41]: (r1_tarski(k9_subset_1(A_39, B_40, C_41), A_39) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(resolution, [status(thm)], [c_83, c_14])).
% 7.80/2.91  tff(c_348, plain, (![C_74, A_75, B_76]: (v2_compts_1(C_74, A_75) | ~v4_pre_topc(C_74, A_75) | ~r1_tarski(C_74, B_76) | ~v2_compts_1(B_76, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.80/2.91  tff(c_2243, plain, (![A_296, B_297, C_298, A_299]: (v2_compts_1(k9_subset_1(A_296, B_297, C_298), A_299) | ~v4_pre_topc(k9_subset_1(A_296, B_297, C_298), A_299) | ~v2_compts_1(A_296, A_299) | ~m1_subset_1(k9_subset_1(A_296, B_297, C_298), k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_subset_1(A_296, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | ~m1_subset_1(C_298, k1_zfmisc_1(A_296)))), inference(resolution, [status(thm)], [c_87, c_348])).
% 7.80/2.91  tff(c_2279, plain, (![B_2, B_59, A_299]: (v2_compts_1(k9_subset_1(B_2, B_59, B_2), A_299) | ~v4_pre_topc(k9_subset_1(B_2, B_59, B_2), A_299) | ~v2_compts_1(B_2, A_299) | ~m1_subset_1(k3_xboole_0(B_59, B_2), k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2243])).
% 7.80/2.91  tff(c_5205, plain, (![B_640, B_641, A_642]: (v2_compts_1(k3_xboole_0(B_640, B_641), A_642) | ~v4_pre_topc(k3_xboole_0(B_640, B_641), A_642) | ~v2_compts_1(B_641, A_642) | ~m1_subset_1(k3_xboole_0(B_640, B_641), k1_zfmisc_1(u1_struct_0(A_642))) | ~m1_subset_1(B_641, k1_zfmisc_1(u1_struct_0(A_642))) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | ~m1_subset_1(B_641, k1_zfmisc_1(B_641)))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_240, c_2279])).
% 7.80/2.91  tff(c_5260, plain, (![B_50]: (v2_compts_1(k3_xboole_0(B_50, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_50, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_138, c_5205])).
% 7.80/2.91  tff(c_5314, plain, (![B_50]: (v2_compts_1(k3_xboole_0(B_50, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_50, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_26, c_5260])).
% 7.80/2.91  tff(c_5579, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5314])).
% 7.80/2.91  tff(c_5582, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_5579])).
% 7.80/2.91  tff(c_5586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5582])).
% 7.80/2.91  tff(c_5838, plain, (![B_668]: (v2_compts_1(k3_xboole_0(B_668, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_668, '#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_5314])).
% 7.80/2.91  tff(c_5917, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_726, c_5838])).
% 7.80/2.91  tff(c_5982, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_159, c_5917])).
% 7.80/2.91  tff(c_5984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_5982])).
% 7.80/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.91  
% 7.80/2.91  Inference rules
% 7.80/2.91  ----------------------
% 7.80/2.91  #Ref     : 0
% 7.80/2.91  #Sup     : 1419
% 7.80/2.91  #Fact    : 0
% 7.80/2.91  #Define  : 0
% 7.80/2.91  #Split   : 7
% 7.80/2.91  #Chain   : 0
% 7.80/2.91  #Close   : 0
% 7.80/2.91  
% 7.80/2.91  Ordering : KBO
% 7.80/2.91  
% 7.80/2.91  Simplification rules
% 7.80/2.91  ----------------------
% 7.80/2.91  #Subsume      : 153
% 7.80/2.91  #Demod        : 1951
% 7.80/2.91  #Tautology    : 347
% 7.80/2.91  #SimpNegUnit  : 1
% 7.80/2.91  #BackRed      : 1
% 7.80/2.91  
% 7.80/2.91  #Partial instantiations: 0
% 7.80/2.91  #Strategies tried      : 1
% 7.80/2.91  
% 7.80/2.91  Timing (in seconds)
% 7.80/2.91  ----------------------
% 7.80/2.91  Preprocessing        : 0.33
% 7.80/2.91  Parsing              : 0.18
% 7.80/2.91  CNF conversion       : 0.02
% 7.80/2.91  Main loop            : 1.76
% 7.80/2.91  Inferencing          : 0.58
% 7.80/2.91  Reduction            : 0.68
% 7.80/2.91  Demodulation         : 0.55
% 7.80/2.91  BG Simplification    : 0.07
% 7.80/2.91  Subsumption          : 0.34
% 7.80/2.91  Abstraction          : 0.09
% 7.80/2.91  MUC search           : 0.00
% 7.80/2.91  Cooper               : 0.00
% 7.80/2.91  Total                : 2.12
% 7.80/2.91  Index Insertion      : 0.00
% 7.80/2.91  Index Deletion       : 0.00
% 7.80/2.91  Index Matching       : 0.00
% 7.80/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
