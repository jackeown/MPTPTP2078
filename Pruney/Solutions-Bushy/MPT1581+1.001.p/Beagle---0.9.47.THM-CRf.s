%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 ( 450 expanded)
%              Number of equality atoms :    4 (  58 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_yellow_0(B,A)
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( E = C
                                & F = D
                                & r1_orders_2(B,E,F) )
                             => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_yellow_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_55,plain,(
    ! [B_83,A_84] :
      ( l1_orders_2(B_83)
      | ~ m1_yellow_0(B_83,A_84)
      | ~ l1_orders_2(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_61,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_30,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_28,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_26,plain,(
    r1_orders_2('#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_45,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_26])).

tff(c_24,plain,(
    ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_orders_2(B_3),u1_orders_2(A_1))
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [B_116,C_117,A_118] :
      ( r2_hidden(k4_tarski(B_116,C_117),u1_orders_2(A_118))
      | ~ r1_orders_2(A_118,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_118))
      | ~ m1_subset_1(B_116,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_95,C_96,B_97] :
      ( m1_subset_1(A_95,C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    ! [A_95,B_17,A_16] :
      ( m1_subset_1(A_95,B_17)
      | ~ r2_hidden(A_95,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_216,plain,(
    ! [B_146,C_147,B_148,A_149] :
      ( m1_subset_1(k4_tarski(B_146,C_147),B_148)
      | ~ r1_tarski(u1_orders_2(A_149),B_148)
      | ~ r1_orders_2(A_149,B_146,C_147)
      | ~ m1_subset_1(C_147,u1_struct_0(A_149))
      | ~ m1_subset_1(B_146,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149) ) ),
    inference(resolution,[status(thm)],[c_106,c_79])).

tff(c_220,plain,(
    ! [B_150,C_151,A_152,B_153] :
      ( m1_subset_1(k4_tarski(B_150,C_151),u1_orders_2(A_152))
      | ~ r1_orders_2(B_153,B_150,C_151)
      | ~ m1_subset_1(C_151,u1_struct_0(B_153))
      | ~ m1_subset_1(B_150,u1_struct_0(B_153))
      | ~ m1_yellow_0(B_153,A_152)
      | ~ l1_orders_2(B_153)
      | ~ l1_orders_2(A_152) ) ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_222,plain,(
    ! [A_152] :
      ( m1_subset_1(k4_tarski('#skF_3','#skF_4'),u1_orders_2(A_152))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0('#skF_2',A_152)
      | ~ l1_orders_2('#skF_2')
      | ~ l1_orders_2(A_152) ) ),
    inference(resolution,[status(thm)],[c_45,c_220])).

tff(c_226,plain,(
    ! [A_154] :
      ( m1_subset_1(k4_tarski('#skF_3','#skF_4'),u1_orders_2(A_154))
      | ~ m1_yellow_0('#skF_2',A_154)
      | ~ l1_orders_2(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_43,c_44,c_222])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [A_125,B_126,C_127] :
      ( r1_orders_2(A_125,B_126,C_127)
      | ~ r2_hidden(k4_tarski(B_126,C_127),u1_orders_2(A_125))
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_125,B_126,C_127] :
      ( r1_orders_2(A_125,B_126,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | v1_xboole_0(u1_orders_2(A_125))
      | ~ m1_subset_1(k4_tarski(B_126,C_127),u1_orders_2(A_125)) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_241,plain,(
    ! [A_157] :
      ( r1_orders_2(A_157,'#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_157))
      | ~ m1_subset_1('#skF_3',u1_struct_0(A_157))
      | v1_xboole_0(u1_orders_2(A_157))
      | ~ m1_yellow_0('#skF_2',A_157)
      | ~ l1_orders_2(A_157) ) ),
    inference(resolution,[status(thm)],[c_226,c_158])).

tff(c_244,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_orders_2('#skF_1'))
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_241])).

tff(c_250,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | v1_xboole_0(u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_244])).

tff(c_251,plain,(
    v1_xboole_0(u1_orders_2('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_250])).

tff(c_68,plain,(
    ! [C_89,B_90,A_91] :
      ( ~ v1_xboole_0(C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_71,plain,(
    ! [B_17,A_91,A_16] :
      ( ~ v1_xboole_0(B_17)
      | ~ r2_hidden(A_91,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_210,plain,(
    ! [B_135,A_136,B_137,C_138] :
      ( ~ v1_xboole_0(B_135)
      | ~ r1_tarski(u1_orders_2(A_136),B_135)
      | ~ r1_orders_2(A_136,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136) ) ),
    inference(resolution,[status(thm)],[c_106,c_71])).

tff(c_213,plain,(
    ! [A_1,B_3,B_137,C_138] :
      ( ~ v1_xboole_0(u1_orders_2(A_1))
      | ~ r1_orders_2(B_3,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(B_3))
      | ~ m1_subset_1(B_137,u1_struct_0(B_3))
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_256,plain,(
    ! [B_3,B_137,C_138] :
      ( ~ r1_orders_2(B_3,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(B_3))
      | ~ m1_subset_1(B_137,u1_struct_0(B_3))
      | ~ m1_yellow_0(B_3,'#skF_1')
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_251,c_213])).

tff(c_277,plain,(
    ! [B_161,B_162,C_163] :
      ( ~ r1_orders_2(B_161,B_162,C_163)
      | ~ m1_subset_1(C_163,u1_struct_0(B_161))
      | ~ m1_subset_1(B_162,u1_struct_0(B_161))
      | ~ m1_yellow_0(B_161,'#skF_1')
      | ~ l1_orders_2(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_256])).

tff(c_279,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_277])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40,c_43,c_44,c_279])).

%------------------------------------------------------------------------------
