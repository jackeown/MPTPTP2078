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
% DateTime   : Thu Dec  3 10:25:37 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 158 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 380 expanded)
%              Number of equality atoms :   20 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_1 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_50,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [A_17] :
      ( r2_hidden(u1_struct_0(A_17),u1_pre_topc(A_17))
      | ~ v2_pre_topc(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_pre_topc(A_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_12] : k3_tarski(k1_zfmisc_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),A_9)
      | r1_tarski(k3_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    ! [C_56,A_57,B_58] :
      ( r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_418,plain,(
    ! [A_106,B_107,A_108] :
      ( r2_hidden('#skF_2'(A_106,B_107),A_108)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(A_108))
      | r1_tarski(k3_tarski(A_106),B_107) ) ),
    inference(resolution,[status(thm)],[c_16,c_141])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [A_50,B_51] :
      ( ~ r1_tarski('#skF_2'(A_50,B_51),B_51)
      | r1_tarski(k3_tarski(A_50),B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_50,B_8] :
      ( r1_tarski(k3_tarski(A_50),k3_tarski(B_8))
      | ~ r2_hidden('#skF_2'(A_50,k3_tarski(B_8)),B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_454,plain,(
    ! [A_109,A_110] :
      ( ~ m1_subset_1(A_109,k1_zfmisc_1(A_110))
      | r1_tarski(k3_tarski(A_109),k3_tarski(A_110)) ) ),
    inference(resolution,[status(thm)],[c_418,c_133])).

tff(c_90,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [B_8,A_7] :
      ( k3_tarski(B_8) = A_7
      | ~ r1_tarski(k3_tarski(B_8),A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_579,plain,(
    ! [A_128,A_127] :
      ( k3_tarski(A_128) = k3_tarski(A_127)
      | ~ r2_hidden(k3_tarski(A_127),A_128)
      | ~ m1_subset_1(A_128,k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_454,c_95])).

tff(c_582,plain,(
    ! [A_12,A_128] :
      ( k3_tarski(k1_zfmisc_1(A_12)) = k3_tarski(A_128)
      | ~ r2_hidden(A_12,A_128)
      | ~ m1_subset_1(A_128,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_579])).

tff(c_605,plain,(
    ! [A_130,A_131] :
      ( k3_tarski(A_130) = A_131
      | ~ r2_hidden(A_131,A_130)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(k1_zfmisc_1(A_131))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_582])).

tff(c_652,plain,(
    ! [A_137] :
      ( k3_tarski(u1_pre_topc(A_137)) = u1_struct_0(A_137)
      | ~ r2_hidden(u1_struct_0(A_137),u1_pre_topc(A_137))
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_58,c_605])).

tff(c_656,plain,(
    ! [A_17] :
      ( k3_tarski(u1_pre_topc(A_17)) = u1_struct_0(A_17)
      | ~ v2_pre_topc(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_56,c_652])).

tff(c_657,plain,(
    ! [A_138] :
      ( k3_tarski(u1_pre_topc(A_138)) = u1_struct_0(A_138)
      | ~ v2_pre_topc(A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_56,c_652])).

tff(c_60,plain,(
    ! [A_32] :
      ( k4_yellow_0(k2_yellow_1(A_32)) = k3_tarski(A_32)
      | ~ r2_hidden(k3_tarski(A_32),A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1665,plain,(
    ! [A_291] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_291))) = k3_tarski(u1_pre_topc(A_291))
      | ~ r2_hidden(u1_struct_0(A_291),u1_pre_topc(A_291))
      | v1_xboole_0(u1_pre_topc(A_291))
      | ~ v2_pre_topc(A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_60])).

tff(c_1670,plain,(
    ! [A_292] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_292))) = k3_tarski(u1_pre_topc(A_292))
      | v1_xboole_0(u1_pre_topc(A_292))
      | ~ v2_pre_topc(A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(resolution,[status(thm)],[c_56,c_1665])).

tff(c_62,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_6'))) != u1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1676,plain,
    ( k3_tarski(u1_pre_topc('#skF_6')) != u1_struct_0('#skF_6')
    | v1_xboole_0(u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_62])).

tff(c_1682,plain,
    ( k3_tarski(u1_pre_topc('#skF_6')) != u1_struct_0('#skF_6')
    | v1_xboole_0(u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1676])).

tff(c_1684,plain,(
    k3_tarski(u1_pre_topc('#skF_6')) != u1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1682])).

tff(c_1687,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_1684])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1687])).

tff(c_1692,plain,(
    v1_xboole_0(u1_pre_topc('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1682])).

tff(c_135,plain,(
    ! [A_54] :
      ( r2_hidden(u1_struct_0(A_54),u1_pre_topc(A_54))
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(u1_pre_topc(A_54))
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_1700,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1692,c_139])).

tff(c_1706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_1 > #skF_6 > #skF_3 > #skF_2
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.51/1.79  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.51/1.79  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.51/1.79  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.79  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.51/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.79  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.51/1.79  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.51/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.79  
% 4.63/1.80  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 4.63/1.80  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 4.63/1.80  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.63/1.80  tff(f_50, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.63/1.80  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 4.63/1.80  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.63/1.80  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.63/1.80  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.80  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 4.63/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.63/1.80  tff(c_64, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.63/1.80  tff(c_66, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.63/1.80  tff(c_56, plain, (![A_17]: (r2_hidden(u1_struct_0(A_17), u1_pre_topc(A_17)) | ~v2_pre_topc(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.63/1.80  tff(c_58, plain, (![A_31]: (m1_subset_1(u1_pre_topc(A_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.63/1.80  tff(c_18, plain, (![A_12]: (k3_tarski(k1_zfmisc_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.80  tff(c_16, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), A_9) | r1_tarski(k3_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.80  tff(c_141, plain, (![C_56, A_57, B_58]: (r2_hidden(C_56, A_57) | ~r2_hidden(C_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.63/1.80  tff(c_418, plain, (![A_106, B_107, A_108]: (r2_hidden('#skF_2'(A_106, B_107), A_108) | ~m1_subset_1(A_106, k1_zfmisc_1(A_108)) | r1_tarski(k3_tarski(A_106), B_107))), inference(resolution, [status(thm)], [c_16, c_141])).
% 4.63/1.80  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.80  tff(c_129, plain, (![A_50, B_51]: (~r1_tarski('#skF_2'(A_50, B_51), B_51) | r1_tarski(k3_tarski(A_50), B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.80  tff(c_133, plain, (![A_50, B_8]: (r1_tarski(k3_tarski(A_50), k3_tarski(B_8)) | ~r2_hidden('#skF_2'(A_50, k3_tarski(B_8)), B_8))), inference(resolution, [status(thm)], [c_12, c_129])).
% 4.63/1.80  tff(c_454, plain, (![A_109, A_110]: (~m1_subset_1(A_109, k1_zfmisc_1(A_110)) | r1_tarski(k3_tarski(A_109), k3_tarski(A_110)))), inference(resolution, [status(thm)], [c_418, c_133])).
% 4.63/1.80  tff(c_90, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.80  tff(c_95, plain, (![B_8, A_7]: (k3_tarski(B_8)=A_7 | ~r1_tarski(k3_tarski(B_8), A_7) | ~r2_hidden(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_90])).
% 4.63/1.80  tff(c_579, plain, (![A_128, A_127]: (k3_tarski(A_128)=k3_tarski(A_127) | ~r2_hidden(k3_tarski(A_127), A_128) | ~m1_subset_1(A_128, k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_454, c_95])).
% 4.63/1.80  tff(c_582, plain, (![A_12, A_128]: (k3_tarski(k1_zfmisc_1(A_12))=k3_tarski(A_128) | ~r2_hidden(A_12, A_128) | ~m1_subset_1(A_128, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_579])).
% 4.63/1.80  tff(c_605, plain, (![A_130, A_131]: (k3_tarski(A_130)=A_131 | ~r2_hidden(A_131, A_130) | ~m1_subset_1(A_130, k1_zfmisc_1(k1_zfmisc_1(A_131))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_582])).
% 4.63/1.80  tff(c_652, plain, (![A_137]: (k3_tarski(u1_pre_topc(A_137))=u1_struct_0(A_137) | ~r2_hidden(u1_struct_0(A_137), u1_pre_topc(A_137)) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_58, c_605])).
% 4.63/1.80  tff(c_656, plain, (![A_17]: (k3_tarski(u1_pre_topc(A_17))=u1_struct_0(A_17) | ~v2_pre_topc(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_56, c_652])).
% 4.63/1.80  tff(c_657, plain, (![A_138]: (k3_tarski(u1_pre_topc(A_138))=u1_struct_0(A_138) | ~v2_pre_topc(A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_56, c_652])).
% 4.63/1.80  tff(c_60, plain, (![A_32]: (k4_yellow_0(k2_yellow_1(A_32))=k3_tarski(A_32) | ~r2_hidden(k3_tarski(A_32), A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.63/1.80  tff(c_1665, plain, (![A_291]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_291)))=k3_tarski(u1_pre_topc(A_291)) | ~r2_hidden(u1_struct_0(A_291), u1_pre_topc(A_291)) | v1_xboole_0(u1_pre_topc(A_291)) | ~v2_pre_topc(A_291) | ~l1_pre_topc(A_291))), inference(superposition, [status(thm), theory('equality')], [c_657, c_60])).
% 4.63/1.80  tff(c_1670, plain, (![A_292]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_292)))=k3_tarski(u1_pre_topc(A_292)) | v1_xboole_0(u1_pre_topc(A_292)) | ~v2_pre_topc(A_292) | ~l1_pre_topc(A_292))), inference(resolution, [status(thm)], [c_56, c_1665])).
% 4.63/1.80  tff(c_62, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_6')))!=u1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.63/1.80  tff(c_1676, plain, (k3_tarski(u1_pre_topc('#skF_6'))!=u1_struct_0('#skF_6') | v1_xboole_0(u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1670, c_62])).
% 4.63/1.80  tff(c_1682, plain, (k3_tarski(u1_pre_topc('#skF_6'))!=u1_struct_0('#skF_6') | v1_xboole_0(u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1676])).
% 4.63/1.80  tff(c_1684, plain, (k3_tarski(u1_pre_topc('#skF_6'))!=u1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1682])).
% 4.63/1.80  tff(c_1687, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_656, c_1684])).
% 4.63/1.80  tff(c_1691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1687])).
% 4.63/1.80  tff(c_1692, plain, (v1_xboole_0(u1_pre_topc('#skF_6'))), inference(splitRight, [status(thm)], [c_1682])).
% 4.63/1.80  tff(c_135, plain, (![A_54]: (r2_hidden(u1_struct_0(A_54), u1_pre_topc(A_54)) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.63/1.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.80  tff(c_139, plain, (![A_54]: (~v1_xboole_0(u1_pre_topc(A_54)) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_135, c_2])).
% 4.63/1.80  tff(c_1700, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1692, c_139])).
% 4.63/1.80  tff(c_1706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1700])).
% 4.63/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.80  
% 4.63/1.80  Inference rules
% 4.63/1.80  ----------------------
% 4.63/1.80  #Ref     : 0
% 4.63/1.80  #Sup     : 374
% 4.63/1.80  #Fact    : 0
% 4.63/1.80  #Define  : 0
% 4.63/1.80  #Split   : 1
% 4.63/1.80  #Chain   : 0
% 4.63/1.80  #Close   : 0
% 4.63/1.80  
% 4.63/1.80  Ordering : KBO
% 4.63/1.80  
% 4.63/1.80  Simplification rules
% 4.63/1.80  ----------------------
% 4.63/1.80  #Subsume      : 89
% 4.63/1.80  #Demod        : 63
% 4.63/1.80  #Tautology    : 45
% 4.63/1.80  #SimpNegUnit  : 0
% 4.63/1.80  #BackRed      : 0
% 4.63/1.80  
% 4.63/1.80  #Partial instantiations: 0
% 4.63/1.80  #Strategies tried      : 1
% 4.63/1.80  
% 4.63/1.80  Timing (in seconds)
% 4.63/1.80  ----------------------
% 4.63/1.81  Preprocessing        : 0.31
% 4.63/1.81  Parsing              : 0.17
% 4.63/1.81  CNF conversion       : 0.02
% 4.63/1.81  Main loop            : 0.72
% 4.63/1.81  Inferencing          : 0.26
% 4.63/1.81  Reduction            : 0.16
% 4.63/1.81  Demodulation         : 0.10
% 4.63/1.81  BG Simplification    : 0.03
% 4.63/1.81  Subsumption          : 0.21
% 4.63/1.81  Abstraction          : 0.03
% 4.63/1.81  MUC search           : 0.00
% 4.63/1.81  Cooper               : 0.00
% 4.63/1.81  Total                : 1.06
% 4.63/1.81  Index Insertion      : 0.00
% 4.63/1.81  Index Deletion       : 0.00
% 4.63/1.81  Index Matching       : 0.00
% 4.63/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
