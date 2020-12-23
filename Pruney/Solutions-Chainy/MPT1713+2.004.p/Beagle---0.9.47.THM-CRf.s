%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 8.86s
% Output     : CNFRefutation 9.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 589 expanded)
%              Number of leaves         :   43 ( 213 expanded)
%              Depth                    :   16
%              Number of atoms          :  228 (1584 expanded)
%              Number of equality atoms :   39 ( 151 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_133,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_289,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(B_70,A_71)
      | ~ r1_xboole_0(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [A_9] : r1_xboole_0(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_136,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = A_76
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_136])).

tff(c_319,plain,(
    ! [B_93] : k3_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_143])).

tff(c_337,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_144,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_315,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_289])).

tff(c_428,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_315])).

tff(c_273,plain,(
    ! [A_87,B_88] :
      ( r1_xboole_0(A_87,B_88)
      | k4_xboole_0(A_87,B_88) != A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_280,plain,(
    ! [B_88,A_87] :
      ( r1_xboole_0(B_88,A_87)
      | k4_xboole_0(A_87,B_88) != A_87 ) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_171,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_177,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_171])).

tff(c_184,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_177])).

tff(c_48,plain,(
    ! [A_53] :
      ( l1_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_80,plain,(
    ! [A_69] :
      ( u1_struct_0(A_69) = k2_struct_0(A_69)
      | ~ l1_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_191,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_84])).

tff(c_207,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(u1_struct_0(A_84))
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_210,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_207])).

tff(c_217,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_210])).

tff(c_220,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_223,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_223])).

tff(c_229,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_389,plain,(
    ! [A_97,B_98] :
      ( r1_tsep_1(A_97,B_98)
      | ~ r1_xboole_0(u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_398,plain,(
    ! [B_98] :
      ( r1_tsep_1('#skF_5',B_98)
      | ~ r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_98))
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_389])).

tff(c_5711,plain,(
    ! [B_285] :
      ( r1_tsep_1('#skF_5',B_285)
      | ~ r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_285))
      | ~ l1_struct_0(B_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_398])).

tff(c_5720,plain,
    ( r1_tsep_1('#skF_5','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_5711])).

tff(c_5730,plain,
    ( r1_tsep_1('#skF_5','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_5720])).

tff(c_5735,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5730])).

tff(c_5738,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_280,c_5735])).

tff(c_5743,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_5738])).

tff(c_64,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_180,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_187,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_180])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5520,plain,(
    ! [B_275,A_276] :
      ( r1_tarski(k2_struct_0(B_275),k2_struct_0(A_276))
      | ~ m1_pre_topc(B_275,A_276)
      | ~ l1_pre_topc(B_275)
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8609,plain,(
    ! [B_399,A_400] :
      ( k3_xboole_0(k2_struct_0(B_399),k2_struct_0(A_400)) = k2_struct_0(B_399)
      | ~ m1_pre_topc(B_399,A_400)
      | ~ l1_pre_topc(B_399)
      | ~ l1_pre_topc(A_400) ) ),
    inference(resolution,[status(thm)],[c_5520,c_8])).

tff(c_10324,plain,(
    ! [A_444,B_445] :
      ( k3_xboole_0(k2_struct_0(A_444),k2_struct_0(B_445)) = k2_struct_0(B_445)
      | ~ m1_pre_topc(B_445,A_444)
      | ~ l1_pre_topc(B_445)
      | ~ l1_pre_topc(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_2])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_195,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_187,c_84])).

tff(c_213,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_207])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_213])).

tff(c_235,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_246,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_235])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_246])).

tff(c_252,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_60,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_79,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_5425,plain,(
    ! [A_273,B_274] :
      ( r1_xboole_0(u1_struct_0(A_273),u1_struct_0(B_274))
      | ~ r1_tsep_1(A_273,B_274)
      | ~ l1_struct_0(B_274)
      | ~ l1_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5436,plain,(
    ! [B_274] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_274))
      | ~ r1_tsep_1('#skF_5',B_274)
      | ~ l1_struct_0(B_274)
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_5425])).

tff(c_5747,plain,(
    ! [B_289] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_289))
      | ~ r1_tsep_1('#skF_5',B_289)
      | ~ l1_struct_0(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_5436])).

tff(c_5761,plain,
    ( r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_5747])).

tff(c_5772,plain,(
    r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_79,c_5761])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5810,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5772,c_14])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5833,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) = k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5810,c_10])).

tff(c_5837,plain,(
    k3_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_428,c_5833])).

tff(c_10357,plain,
    ( k2_struct_0('#skF_5') = k1_xboole_0
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10324,c_5837])).

tff(c_10405,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_184,c_62,c_10357])).

tff(c_10407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5743,c_10405])).

tff(c_10409,plain,(
    r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5730])).

tff(c_10417,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10409,c_14])).

tff(c_10421,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_10417])).

tff(c_228,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_10431,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_228])).

tff(c_10443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10431])).

tff(c_10445,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_10520,plain,(
    ! [B_459,A_460] :
      ( l1_pre_topc(B_459)
      | ~ m1_pre_topc(B_459,A_460)
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10529,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_10520])).

tff(c_10536,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10529])).

tff(c_10455,plain,(
    ! [A_449] :
      ( u1_struct_0(A_449) = k2_struct_0(A_449)
      | ~ l1_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10459,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_48,c_10455])).

tff(c_10544,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10536,c_10459])).

tff(c_10581,plain,(
    ! [A_463] :
      ( ~ v1_xboole_0(u1_struct_0(A_463))
      | ~ l1_struct_0(A_463)
      | v2_struct_0(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10587,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10544,c_10581])).

tff(c_10592,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_10587])).

tff(c_10639,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10592])).

tff(c_10642,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_10639])).

tff(c_10646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10536,c_10642])).

tff(c_10648,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10592])).

tff(c_10526,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10520])).

tff(c_10533,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10526])).

tff(c_10540,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10533,c_10459])).

tff(c_10584,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10540,c_10581])).

tff(c_10591,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10584])).

tff(c_10594,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10591])).

tff(c_10627,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_10594])).

tff(c_10631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10533,c_10627])).

tff(c_10633,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10591])).

tff(c_10444,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_10720,plain,(
    ! [B_469,A_470] :
      ( r1_tsep_1(B_469,A_470)
      | ~ r1_tsep_1(A_470,B_469)
      | ~ l1_struct_0(B_469)
      | ~ l1_struct_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10722,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10444,c_10720])).

tff(c_10725,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10648,c_10633,c_10722])).

tff(c_10727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10445,c_10725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.86/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/3.00  
% 8.86/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/3.01  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.86/3.01  
% 8.86/3.01  %Foreground sorts:
% 8.86/3.01  
% 8.86/3.01  
% 8.86/3.01  %Background operators:
% 8.86/3.01  
% 8.86/3.01  
% 8.86/3.01  %Foreground operators:
% 8.86/3.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.86/3.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.86/3.01  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.86/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.86/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.86/3.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.86/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.86/3.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.86/3.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.86/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.86/3.01  tff('#skF_5', type, '#skF_5': $i).
% 8.86/3.01  tff('#skF_6', type, '#skF_6': $i).
% 8.86/3.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.86/3.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.86/3.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.86/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.86/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.86/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.86/3.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.86/3.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.86/3.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.86/3.01  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 8.86/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.86/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.86/3.01  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.86/3.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.86/3.01  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.86/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.86/3.01  
% 9.22/3.03  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.22/3.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.22/3.03  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.22/3.03  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.22/3.03  tff(f_32, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.22/3.03  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.22/3.03  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 9.22/3.03  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.22/3.03  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.22/3.03  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.22/3.03  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.22/3.03  tff(f_97, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 9.22/3.03  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 9.22/3.03  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.22/3.03  tff(f_105, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 9.22/3.03  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 9.22/3.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.22/3.03  tff(c_289, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.22/3.03  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.22/3.03  tff(c_85, plain, (![B_70, A_71]: (r1_xboole_0(B_70, A_71) | ~r1_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.22/3.03  tff(c_88, plain, (![A_9]: (r1_xboole_0(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_12, c_85])).
% 9.22/3.03  tff(c_136, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=A_76 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.22/3.03  tff(c_143, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_136])).
% 9.22/3.03  tff(c_319, plain, (![B_93]: (k3_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_289, c_143])).
% 9.22/3.03  tff(c_337, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 9.22/3.03  tff(c_144, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(resolution, [status(thm)], [c_12, c_136])).
% 9.22/3.03  tff(c_315, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_289])).
% 9.22/3.03  tff(c_428, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_315])).
% 9.22/3.03  tff(c_273, plain, (![A_87, B_88]: (r1_xboole_0(A_87, B_88) | k4_xboole_0(A_87, B_88)!=A_87)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.22/3.03  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.22/3.03  tff(c_280, plain, (![B_88, A_87]: (r1_xboole_0(B_88, A_87) | k4_xboole_0(A_87, B_88)!=A_87)), inference(resolution, [status(thm)], [c_273, c_6])).
% 9.22/3.03  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_68, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_171, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.22/3.03  tff(c_177, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_171])).
% 9.22/3.03  tff(c_184, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_177])).
% 9.22/3.03  tff(c_48, plain, (![A_53]: (l1_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.22/3.03  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_80, plain, (![A_69]: (u1_struct_0(A_69)=k2_struct_0(A_69) | ~l1_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.22/3.03  tff(c_84, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_48, c_80])).
% 9.22/3.03  tff(c_191, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_184, c_84])).
% 9.22/3.03  tff(c_207, plain, (![A_84]: (~v1_xboole_0(u1_struct_0(A_84)) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.22/3.03  tff(c_210, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_191, c_207])).
% 9.22/3.03  tff(c_217, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_210])).
% 9.22/3.03  tff(c_220, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_217])).
% 9.22/3.03  tff(c_223, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_220])).
% 9.22/3.03  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_223])).
% 9.22/3.03  tff(c_229, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_217])).
% 9.22/3.03  tff(c_389, plain, (![A_97, B_98]: (r1_tsep_1(A_97, B_98) | ~r1_xboole_0(u1_struct_0(A_97), u1_struct_0(B_98)) | ~l1_struct_0(B_98) | ~l1_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.22/3.03  tff(c_398, plain, (![B_98]: (r1_tsep_1('#skF_5', B_98) | ~r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_98)) | ~l1_struct_0(B_98) | ~l1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_389])).
% 9.22/3.03  tff(c_5711, plain, (![B_285]: (r1_tsep_1('#skF_5', B_285) | ~r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_285)) | ~l1_struct_0(B_285))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_398])).
% 9.22/3.03  tff(c_5720, plain, (r1_tsep_1('#skF_5', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_191, c_5711])).
% 9.22/3.03  tff(c_5730, plain, (r1_tsep_1('#skF_5', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_5720])).
% 9.22/3.03  tff(c_5735, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_5730])).
% 9.22/3.03  tff(c_5738, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_280, c_5735])).
% 9.22/3.03  tff(c_5743, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_428, c_5738])).
% 9.22/3.03  tff(c_64, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_180, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_171])).
% 9.22/3.03  tff(c_187, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_180])).
% 9.22/3.03  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_5520, plain, (![B_275, A_276]: (r1_tarski(k2_struct_0(B_275), k2_struct_0(A_276)) | ~m1_pre_topc(B_275, A_276) | ~l1_pre_topc(B_275) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.22/3.03  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.22/3.03  tff(c_8609, plain, (![B_399, A_400]: (k3_xboole_0(k2_struct_0(B_399), k2_struct_0(A_400))=k2_struct_0(B_399) | ~m1_pre_topc(B_399, A_400) | ~l1_pre_topc(B_399) | ~l1_pre_topc(A_400))), inference(resolution, [status(thm)], [c_5520, c_8])).
% 9.22/3.03  tff(c_10324, plain, (![A_444, B_445]: (k3_xboole_0(k2_struct_0(A_444), k2_struct_0(B_445))=k2_struct_0(B_445) | ~m1_pre_topc(B_445, A_444) | ~l1_pre_topc(B_445) | ~l1_pre_topc(A_444))), inference(superposition, [status(thm), theory('equality')], [c_8609, c_2])).
% 9.22/3.03  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_195, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_187, c_84])).
% 9.22/3.03  tff(c_213, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_195, c_207])).
% 9.22/3.03  tff(c_218, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_213])).
% 9.22/3.03  tff(c_235, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_218])).
% 9.22/3.03  tff(c_246, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_235])).
% 9.22/3.03  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_246])).
% 9.22/3.03  tff(c_252, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_218])).
% 9.22/3.03  tff(c_60, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.22/3.03  tff(c_79, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_60])).
% 9.22/3.03  tff(c_5425, plain, (![A_273, B_274]: (r1_xboole_0(u1_struct_0(A_273), u1_struct_0(B_274)) | ~r1_tsep_1(A_273, B_274) | ~l1_struct_0(B_274) | ~l1_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.22/3.03  tff(c_5436, plain, (![B_274]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_274)) | ~r1_tsep_1('#skF_5', B_274) | ~l1_struct_0(B_274) | ~l1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_5425])).
% 9.22/3.03  tff(c_5747, plain, (![B_289]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_289)) | ~r1_tsep_1('#skF_5', B_289) | ~l1_struct_0(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_5436])).
% 9.22/3.03  tff(c_5761, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_195, c_5747])).
% 9.22/3.03  tff(c_5772, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_79, c_5761])).
% 9.22/3.03  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.22/3.03  tff(c_5810, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5772, c_14])).
% 9.22/3.03  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.22/3.03  tff(c_5833, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))=k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5810, c_10])).
% 9.22/3.03  tff(c_5837, plain, (k3_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_428, c_5833])).
% 9.22/3.03  tff(c_10357, plain, (k2_struct_0('#skF_5')=k1_xboole_0 | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10324, c_5837])).
% 9.22/3.03  tff(c_10405, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_187, c_184, c_62, c_10357])).
% 9.22/3.03  tff(c_10407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5743, c_10405])).
% 9.22/3.03  tff(c_10409, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_5730])).
% 9.22/3.03  tff(c_10417, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_10409, c_14])).
% 9.22/3.03  tff(c_10421, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_428, c_10417])).
% 9.22/3.03  tff(c_228, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_217])).
% 9.22/3.03  tff(c_10431, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_228])).
% 9.22/3.03  tff(c_10443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_10431])).
% 9.22/3.03  tff(c_10445, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 9.22/3.03  tff(c_10520, plain, (![B_459, A_460]: (l1_pre_topc(B_459) | ~m1_pre_topc(B_459, A_460) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.22/3.03  tff(c_10529, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_10520])).
% 9.22/3.03  tff(c_10536, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10529])).
% 9.22/3.03  tff(c_10455, plain, (![A_449]: (u1_struct_0(A_449)=k2_struct_0(A_449) | ~l1_struct_0(A_449))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.22/3.03  tff(c_10459, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_48, c_10455])).
% 9.22/3.03  tff(c_10544, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_10536, c_10459])).
% 9.22/3.03  tff(c_10581, plain, (![A_463]: (~v1_xboole_0(u1_struct_0(A_463)) | ~l1_struct_0(A_463) | v2_struct_0(A_463))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.22/3.03  tff(c_10587, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10544, c_10581])).
% 9.22/3.03  tff(c_10592, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_10587])).
% 9.22/3.03  tff(c_10639, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_10592])).
% 9.22/3.03  tff(c_10642, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_10639])).
% 9.22/3.03  tff(c_10646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10536, c_10642])).
% 9.22/3.03  tff(c_10648, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_10592])).
% 9.22/3.03  tff(c_10526, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_10520])).
% 9.22/3.03  tff(c_10533, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10526])).
% 9.22/3.03  tff(c_10540, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_10533, c_10459])).
% 9.22/3.03  tff(c_10584, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10540, c_10581])).
% 9.22/3.03  tff(c_10591, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_10584])).
% 9.22/3.03  tff(c_10594, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_10591])).
% 9.22/3.03  tff(c_10627, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_10594])).
% 9.22/3.03  tff(c_10631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10533, c_10627])).
% 9.22/3.03  tff(c_10633, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_10591])).
% 9.22/3.03  tff(c_10444, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 9.22/3.03  tff(c_10720, plain, (![B_469, A_470]: (r1_tsep_1(B_469, A_470) | ~r1_tsep_1(A_470, B_469) | ~l1_struct_0(B_469) | ~l1_struct_0(A_470))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.22/3.03  tff(c_10722, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_10444, c_10720])).
% 9.22/3.03  tff(c_10725, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10648, c_10633, c_10722])).
% 9.22/3.03  tff(c_10727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10445, c_10725])).
% 9.22/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.03  
% 9.22/3.03  Inference rules
% 9.22/3.03  ----------------------
% 9.22/3.03  #Ref     : 0
% 9.22/3.03  #Sup     : 2381
% 9.22/3.03  #Fact    : 0
% 9.22/3.03  #Define  : 0
% 9.22/3.03  #Split   : 23
% 9.22/3.03  #Chain   : 0
% 9.22/3.03  #Close   : 0
% 9.22/3.03  
% 9.22/3.03  Ordering : KBO
% 9.22/3.03  
% 9.22/3.03  Simplification rules
% 9.22/3.03  ----------------------
% 9.22/3.03  #Subsume      : 601
% 9.22/3.03  #Demod        : 2893
% 9.22/3.03  #Tautology    : 894
% 9.22/3.03  #SimpNegUnit  : 302
% 9.22/3.03  #BackRed      : 22
% 9.22/3.03  
% 9.22/3.03  #Partial instantiations: 0
% 9.22/3.03  #Strategies tried      : 1
% 9.22/3.03  
% 9.22/3.03  Timing (in seconds)
% 9.22/3.03  ----------------------
% 9.22/3.03  Preprocessing        : 0.36
% 9.22/3.03  Parsing              : 0.17
% 9.22/3.03  CNF conversion       : 0.03
% 9.22/3.03  Main loop            : 1.86
% 9.22/3.03  Inferencing          : 0.55
% 9.22/3.03  Reduction            : 0.76
% 9.22/3.03  Demodulation         : 0.59
% 9.22/3.03  BG Simplification    : 0.07
% 9.22/3.03  Subsumption          : 0.37
% 9.22/3.03  Abstraction          : 0.09
% 9.22/3.03  MUC search           : 0.00
% 9.22/3.03  Cooper               : 0.00
% 9.22/3.03  Total                : 2.26
% 9.22/3.03  Index Insertion      : 0.00
% 9.22/3.03  Index Deletion       : 0.00
% 9.22/3.03  Index Matching       : 0.00
% 9.22/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
