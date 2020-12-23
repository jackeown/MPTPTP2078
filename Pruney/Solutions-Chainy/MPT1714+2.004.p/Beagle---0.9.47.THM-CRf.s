%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 261 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  247 (1001 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_151,negated_conjecture,(
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2773,plain,(
    ! [B_298,A_299] :
      ( l1_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2776,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2773])).

tff(c_2788,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2776])).

tff(c_36,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2779,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2773])).

tff(c_2791,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2779])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2638,plain,(
    ! [B_274,A_275] :
      ( l1_pre_topc(B_274)
      | ~ m1_pre_topc(B_274,A_275)
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2650,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2638])).

tff(c_2660,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2650])).

tff(c_2641,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2638])).

tff(c_2653,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2641])).

tff(c_92,plain,(
    ! [B_51,A_52] :
      ( l1_pre_topc(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_114,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_111,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_92])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_115])).

tff(c_118,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_107,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_95])).

tff(c_50,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_77,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_187,plain,(
    ! [B_70,A_71] :
      ( r1_tsep_1(B_70,A_71)
      | ~ r1_tsep_1(A_71,B_70)
      | ~ l1_struct_0(B_70)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_190,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_77,c_187])).

tff(c_191,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_194,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_194])).

tff(c_199,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_201,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_216,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_216])).

tff(c_222,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_200,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_159,plain,(
    ! [B_65,A_66] :
      ( v2_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_171,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_159])).

tff(c_183,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_171])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_510,plain,(
    ! [B_122,C_123,A_124] :
      ( m1_pre_topc(B_122,C_123)
      | ~ r1_tarski(u1_struct_0(B_122),u1_struct_0(C_123))
      | ~ m1_pre_topc(C_123,A_124)
      | ~ m1_pre_topc(B_122,A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_515,plain,(
    ! [B_125,A_126] :
      ( m1_pre_topc(B_125,B_125)
      | ~ m1_pre_topc(B_125,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_30,c_510])).

tff(c_523,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_515])).

tff(c_535,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_523])).

tff(c_684,plain,(
    ! [B_143,C_144,A_145] :
      ( r1_tarski(u1_struct_0(B_143),u1_struct_0(C_144))
      | ~ m1_pre_topc(B_143,C_144)
      | ~ m1_pre_topc(C_144,A_145)
      | ~ m1_pre_topc(B_143,A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_686,plain,(
    ! [B_143] :
      ( r1_tarski(u1_struct_0(B_143),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_143,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_535,c_684])).

tff(c_720,plain,(
    ! [B_146] :
      ( r1_tarski(u1_struct_0(B_146),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_146,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_114,c_686])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_753,plain,(
    ! [B_149] :
      ( k3_xboole_0(u1_struct_0(B_149),u1_struct_0('#skF_6')) = u1_struct_0(B_149)
      | ~ m1_pre_topc(B_149,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_720,c_32])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1151,plain,(
    ! [D_160,B_161] :
      ( r2_hidden(D_160,u1_struct_0('#skF_6'))
      | ~ r2_hidden(D_160,u1_struct_0(B_161))
      | ~ m1_pre_topc(B_161,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_4])).

tff(c_1226,plain,(
    ! [B_161,B_8] :
      ( r2_hidden('#skF_3'(u1_struct_0(B_161),B_8),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_161,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_161),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_1151])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_241,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(u1_struct_0(A_80),u1_struct_0(B_81))
      | ~ r1_tsep_1(A_80,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_315,plain,(
    ! [C_97,B_98,A_99] :
      ( ~ r2_hidden(C_97,u1_struct_0(B_98))
      | ~ r2_hidden(C_97,u1_struct_0(A_99))
      | ~ r1_tsep_1(A_99,B_98)
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_241,c_20])).

tff(c_2236,plain,(
    ! [A_246,B_247,A_248] :
      ( ~ r2_hidden('#skF_3'(A_246,u1_struct_0(B_247)),u1_struct_0(A_248))
      | ~ r1_tsep_1(A_248,B_247)
      | ~ l1_struct_0(B_247)
      | ~ l1_struct_0(A_248)
      | r1_xboole_0(A_246,u1_struct_0(B_247)) ) ),
    inference(resolution,[status(thm)],[c_22,c_315])).

tff(c_2314,plain,(
    ! [B_247,B_161] :
      ( ~ r1_tsep_1('#skF_6',B_247)
      | ~ l1_struct_0(B_247)
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_161,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_161),u1_struct_0(B_247)) ) ),
    inference(resolution,[status(thm)],[c_1226,c_2236])).

tff(c_2528,plain,(
    ! [B_261,B_262] :
      ( ~ r1_tsep_1('#skF_6',B_261)
      | ~ l1_struct_0(B_261)
      | ~ m1_pre_topc(B_262,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_262),u1_struct_0(B_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_2314])).

tff(c_40,plain,(
    ! [A_23,B_25] :
      ( r1_tsep_1(A_23,B_25)
      | ~ r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2585,plain,(
    ! [B_268,B_269] :
      ( r1_tsep_1(B_268,B_269)
      | ~ l1_struct_0(B_268)
      | ~ r1_tsep_1('#skF_6',B_269)
      | ~ l1_struct_0(B_269)
      | ~ m1_pre_topc(B_268,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2528,c_40])).

tff(c_2587,plain,(
    ! [B_268] :
      ( r1_tsep_1(B_268,'#skF_7')
      | ~ l1_struct_0(B_268)
      | ~ l1_struct_0('#skF_7')
      | ~ m1_pre_topc(B_268,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_77,c_2585])).

tff(c_2591,plain,(
    ! [B_270] :
      ( r1_tsep_1(B_270,'#skF_7')
      | ~ l1_struct_0(B_270)
      | ~ m1_pre_topc(B_270,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2587])).

tff(c_52,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2602,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2591,c_76])).

tff(c_2614,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2602])).

tff(c_2617,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2614])).

tff(c_2621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2617])).

tff(c_2623,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2622,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2733,plain,(
    ! [B_293,A_294] :
      ( r1_tsep_1(B_293,A_294)
      | ~ r1_tsep_1(A_294,B_293)
      | ~ l1_struct_0(B_293)
      | ~ l1_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2735,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2622,c_2733])).

tff(c_2738,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2623,c_2735])).

tff(c_2739,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2738])).

tff(c_2742,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2739])).

tff(c_2746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2742])).

tff(c_2747,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2738])).

tff(c_2751,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2747])).

tff(c_2755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2660,c_2751])).

tff(c_2756,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2757,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2863,plain,(
    ! [B_317,A_318] :
      ( r1_tsep_1(B_317,A_318)
      | ~ r1_tsep_1(A_318,B_317)
      | ~ l1_struct_0(B_317)
      | ~ l1_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2867,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2757,c_2863])).

tff(c_2871,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2756,c_2867])).

tff(c_2872,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2871])).

tff(c_2876,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2872])).

tff(c_2880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2791,c_2876])).

tff(c_2881,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2871])).

tff(c_2885,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2881])).

tff(c_2889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.85  
% 4.80/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.85  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.80/1.85  
% 4.80/1.85  %Foreground sorts:
% 4.80/1.85  
% 4.80/1.85  
% 4.80/1.85  %Background operators:
% 4.80/1.85  
% 4.80/1.85  
% 4.80/1.85  %Foreground operators:
% 4.80/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.80/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.80/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.80/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.80/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.80/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.80/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.80/1.85  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.85  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.80/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.80/1.85  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.80/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.85  
% 4.80/1.87  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.80/1.87  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.80/1.87  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.80/1.87  tff(f_99, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.80/1.87  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.80/1.87  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.80/1.87  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.80/1.87  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.80/1.87  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.80/1.87  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.80/1.87  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.80/1.87  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_2773, plain, (![B_298, A_299]: (l1_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.80/1.87  tff(c_2776, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2773])).
% 4.80/1.87  tff(c_2788, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2776])).
% 4.80/1.87  tff(c_36, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.87  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_2779, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2773])).
% 4.80/1.87  tff(c_2791, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2779])).
% 4.80/1.87  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_2638, plain, (![B_274, A_275]: (l1_pre_topc(B_274) | ~m1_pre_topc(B_274, A_275) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.80/1.87  tff(c_2650, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2638])).
% 4.80/1.87  tff(c_2660, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2650])).
% 4.80/1.87  tff(c_2641, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2638])).
% 4.80/1.87  tff(c_2653, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2641])).
% 4.80/1.87  tff(c_92, plain, (![B_51, A_52]: (l1_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.80/1.87  tff(c_104, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_92])).
% 4.80/1.87  tff(c_114, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104])).
% 4.80/1.87  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_111, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_54, c_92])).
% 4.80/1.87  tff(c_115, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_111])).
% 4.80/1.87  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_115])).
% 4.80/1.87  tff(c_118, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 4.80/1.87  tff(c_95, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_92])).
% 4.80/1.87  tff(c_107, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_95])).
% 4.80/1.87  tff(c_50, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_77, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 4.80/1.87  tff(c_187, plain, (![B_70, A_71]: (r1_tsep_1(B_70, A_71) | ~r1_tsep_1(A_71, B_70) | ~l1_struct_0(B_70) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.80/1.87  tff(c_190, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_77, c_187])).
% 4.80/1.87  tff(c_191, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_190])).
% 4.80/1.87  tff(c_194, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_191])).
% 4.80/1.87  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_194])).
% 4.80/1.87  tff(c_199, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_190])).
% 4.80/1.87  tff(c_201, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_199])).
% 4.80/1.87  tff(c_216, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_201])).
% 4.80/1.87  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_216])).
% 4.80/1.87  tff(c_222, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_199])).
% 4.80/1.87  tff(c_200, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_190])).
% 4.80/1.87  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/1.87  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_159, plain, (![B_65, A_66]: (v2_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.80/1.87  tff(c_171, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_159])).
% 4.80/1.87  tff(c_183, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_171])).
% 4.80/1.87  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.80/1.87  tff(c_510, plain, (![B_122, C_123, A_124]: (m1_pre_topc(B_122, C_123) | ~r1_tarski(u1_struct_0(B_122), u1_struct_0(C_123)) | ~m1_pre_topc(C_123, A_124) | ~m1_pre_topc(B_122, A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.80/1.87  tff(c_515, plain, (![B_125, A_126]: (m1_pre_topc(B_125, B_125) | ~m1_pre_topc(B_125, A_126) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126))), inference(resolution, [status(thm)], [c_30, c_510])).
% 4.80/1.87  tff(c_523, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_515])).
% 4.80/1.87  tff(c_535, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_523])).
% 4.80/1.87  tff(c_684, plain, (![B_143, C_144, A_145]: (r1_tarski(u1_struct_0(B_143), u1_struct_0(C_144)) | ~m1_pre_topc(B_143, C_144) | ~m1_pre_topc(C_144, A_145) | ~m1_pre_topc(B_143, A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.80/1.87  tff(c_686, plain, (![B_143]: (r1_tarski(u1_struct_0(B_143), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_143, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_535, c_684])).
% 4.80/1.87  tff(c_720, plain, (![B_146]: (r1_tarski(u1_struct_0(B_146), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_146, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_114, c_686])).
% 4.80/1.87  tff(c_32, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.80/1.87  tff(c_753, plain, (![B_149]: (k3_xboole_0(u1_struct_0(B_149), u1_struct_0('#skF_6'))=u1_struct_0(B_149) | ~m1_pre_topc(B_149, '#skF_6'))), inference(resolution, [status(thm)], [c_720, c_32])).
% 4.80/1.87  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.87  tff(c_1151, plain, (![D_160, B_161]: (r2_hidden(D_160, u1_struct_0('#skF_6')) | ~r2_hidden(D_160, u1_struct_0(B_161)) | ~m1_pre_topc(B_161, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_4])).
% 4.80/1.87  tff(c_1226, plain, (![B_161, B_8]: (r2_hidden('#skF_3'(u1_struct_0(B_161), B_8), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_161, '#skF_6') | r1_xboole_0(u1_struct_0(B_161), B_8))), inference(resolution, [status(thm)], [c_24, c_1151])).
% 4.80/1.87  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/1.87  tff(c_241, plain, (![A_80, B_81]: (r1_xboole_0(u1_struct_0(A_80), u1_struct_0(B_81)) | ~r1_tsep_1(A_80, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.87  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/1.87  tff(c_315, plain, (![C_97, B_98, A_99]: (~r2_hidden(C_97, u1_struct_0(B_98)) | ~r2_hidden(C_97, u1_struct_0(A_99)) | ~r1_tsep_1(A_99, B_98) | ~l1_struct_0(B_98) | ~l1_struct_0(A_99))), inference(resolution, [status(thm)], [c_241, c_20])).
% 4.80/1.87  tff(c_2236, plain, (![A_246, B_247, A_248]: (~r2_hidden('#skF_3'(A_246, u1_struct_0(B_247)), u1_struct_0(A_248)) | ~r1_tsep_1(A_248, B_247) | ~l1_struct_0(B_247) | ~l1_struct_0(A_248) | r1_xboole_0(A_246, u1_struct_0(B_247)))), inference(resolution, [status(thm)], [c_22, c_315])).
% 4.80/1.87  tff(c_2314, plain, (![B_247, B_161]: (~r1_tsep_1('#skF_6', B_247) | ~l1_struct_0(B_247) | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_161, '#skF_6') | r1_xboole_0(u1_struct_0(B_161), u1_struct_0(B_247)))), inference(resolution, [status(thm)], [c_1226, c_2236])).
% 4.80/1.87  tff(c_2528, plain, (![B_261, B_262]: (~r1_tsep_1('#skF_6', B_261) | ~l1_struct_0(B_261) | ~m1_pre_topc(B_262, '#skF_6') | r1_xboole_0(u1_struct_0(B_262), u1_struct_0(B_261)))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_2314])).
% 4.80/1.87  tff(c_40, plain, (![A_23, B_25]: (r1_tsep_1(A_23, B_25) | ~r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.87  tff(c_2585, plain, (![B_268, B_269]: (r1_tsep_1(B_268, B_269) | ~l1_struct_0(B_268) | ~r1_tsep_1('#skF_6', B_269) | ~l1_struct_0(B_269) | ~m1_pre_topc(B_268, '#skF_6'))), inference(resolution, [status(thm)], [c_2528, c_40])).
% 4.80/1.87  tff(c_2587, plain, (![B_268]: (r1_tsep_1(B_268, '#skF_7') | ~l1_struct_0(B_268) | ~l1_struct_0('#skF_7') | ~m1_pre_topc(B_268, '#skF_6'))), inference(resolution, [status(thm)], [c_77, c_2585])).
% 4.80/1.87  tff(c_2591, plain, (![B_270]: (r1_tsep_1(B_270, '#skF_7') | ~l1_struct_0(B_270) | ~m1_pre_topc(B_270, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2587])).
% 4.80/1.87  tff(c_52, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.80/1.87  tff(c_76, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 4.80/1.87  tff(c_2602, plain, (~l1_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2591, c_76])).
% 4.80/1.87  tff(c_2614, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2602])).
% 4.80/1.87  tff(c_2617, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2614])).
% 4.80/1.87  tff(c_2621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_2617])).
% 4.80/1.87  tff(c_2623, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 4.80/1.87  tff(c_2622, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 4.80/1.87  tff(c_2733, plain, (![B_293, A_294]: (r1_tsep_1(B_293, A_294) | ~r1_tsep_1(A_294, B_293) | ~l1_struct_0(B_293) | ~l1_struct_0(A_294))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.80/1.87  tff(c_2735, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2622, c_2733])).
% 4.80/1.87  tff(c_2738, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2623, c_2735])).
% 4.80/1.87  tff(c_2739, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_2738])).
% 4.80/1.87  tff(c_2742, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_2739])).
% 4.80/1.87  tff(c_2746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2742])).
% 4.80/1.87  tff(c_2747, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_2738])).
% 4.80/1.87  tff(c_2751, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2747])).
% 4.80/1.87  tff(c_2755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2660, c_2751])).
% 4.80/1.87  tff(c_2756, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 4.80/1.87  tff(c_2757, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 4.80/1.87  tff(c_2863, plain, (![B_317, A_318]: (r1_tsep_1(B_317, A_318) | ~r1_tsep_1(A_318, B_317) | ~l1_struct_0(B_317) | ~l1_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.80/1.87  tff(c_2867, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2757, c_2863])).
% 4.80/1.87  tff(c_2871, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2756, c_2867])).
% 4.80/1.87  tff(c_2872, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2871])).
% 4.80/1.87  tff(c_2876, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2872])).
% 4.80/1.87  tff(c_2880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2791, c_2876])).
% 4.80/1.87  tff(c_2881, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_2871])).
% 4.80/1.87  tff(c_2885, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_2881])).
% 4.80/1.87  tff(c_2889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2885])).
% 4.80/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  Inference rules
% 4.80/1.87  ----------------------
% 4.80/1.87  #Ref     : 0
% 4.80/1.87  #Sup     : 617
% 4.80/1.87  #Fact    : 0
% 4.80/1.87  #Define  : 0
% 4.80/1.87  #Split   : 15
% 4.80/1.87  #Chain   : 0
% 4.80/1.87  #Close   : 0
% 4.80/1.87  
% 4.80/1.87  Ordering : KBO
% 4.80/1.87  
% 4.80/1.87  Simplification rules
% 4.80/1.87  ----------------------
% 4.80/1.87  #Subsume      : 117
% 4.80/1.87  #Demod        : 234
% 4.80/1.87  #Tautology    : 75
% 4.80/1.87  #SimpNegUnit  : 2
% 4.80/1.87  #BackRed      : 0
% 4.80/1.87  
% 4.80/1.87  #Partial instantiations: 0
% 4.80/1.87  #Strategies tried      : 1
% 4.80/1.87  
% 4.80/1.87  Timing (in seconds)
% 4.80/1.87  ----------------------
% 4.80/1.87  Preprocessing        : 0.31
% 4.80/1.87  Parsing              : 0.17
% 4.80/1.87  CNF conversion       : 0.02
% 4.80/1.87  Main loop            : 0.78
% 4.80/1.87  Inferencing          : 0.28
% 4.80/1.87  Reduction            : 0.21
% 4.80/1.87  Demodulation         : 0.14
% 4.80/1.87  BG Simplification    : 0.04
% 4.80/1.87  Subsumption          : 0.20
% 4.80/1.87  Abstraction          : 0.03
% 4.80/1.87  MUC search           : 0.00
% 4.80/1.87  Cooper               : 0.00
% 4.80/1.87  Total                : 1.14
% 4.80/1.87  Index Insertion      : 0.00
% 4.80/1.87  Index Deletion       : 0.00
% 4.80/1.87  Index Matching       : 0.00
% 4.80/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
