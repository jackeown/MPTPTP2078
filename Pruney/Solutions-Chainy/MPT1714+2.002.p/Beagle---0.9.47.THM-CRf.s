%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 534 expanded)
%              Number of leaves         :   29 ( 192 expanded)
%              Depth                    :   16
%              Number of atoms          :  297 (2364 expanded)
%              Number of equality atoms :    1 (   9 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_145,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_50,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1005,plain,(
    ! [B_197,A_198] :
      ( l1_pre_topc(B_197)
      | ~ m1_pre_topc(B_197,A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1017,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1005])).

tff(c_1027,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1017])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1008,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1005])).

tff(c_1020,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1008])).

tff(c_896,plain,(
    ! [B_175,A_176] :
      ( l1_pre_topc(B_175)
      | ~ m1_pre_topc(B_175,A_176)
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_899,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_896])).

tff(c_911,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_899])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_902,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_896])).

tff(c_914,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_902])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,(
    ! [B_45,A_46] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_86,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_76])).

tff(c_83,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_83])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    ! [B_90,C_91,A_92] :
      ( m1_pre_topc(B_90,C_91)
      | ~ r1_tarski(u1_struct_0(B_90),u1_struct_0(C_91))
      | ~ m1_pre_topc(C_91,A_92)
      | ~ m1_pre_topc(B_90,A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_217,plain,(
    ! [B_93,A_94] :
      ( m1_pre_topc(B_93,B_93)
      | ~ m1_pre_topc(B_93,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_18,c_212])).

tff(c_221,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_217])).

tff(c_231,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_221])).

tff(c_118,plain,(
    ! [B_63,A_64] :
      ( v2_pre_topc(B_63)
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_136,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_124])).

tff(c_290,plain,(
    ! [B_95,C_96,A_97] :
      ( r1_tarski(u1_struct_0(B_95),u1_struct_0(C_96))
      | ~ m1_pre_topc(B_95,C_96)
      | ~ m1_pre_topc(C_96,A_97)
      | ~ m1_pre_topc(B_95,A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_292,plain,(
    ! [B_95] :
      ( r1_tarski(u1_struct_0(B_95),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_95,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_231,c_290])).

tff(c_307,plain,(
    ! [B_95] :
      ( r1_tarski(u1_struct_0(B_95),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_95,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_88,c_292])).

tff(c_326,plain,(
    ! [B_98] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_98,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_88,c_292])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    ! [A_72,B_73,B_74] :
      ( r2_hidden('#skF_2'(A_72,B_73),B_74)
      | ~ r1_tarski(B_73,B_74)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_72,B_73,B_2,B_74] :
      ( r2_hidden('#skF_2'(A_72,B_73),B_2)
      | ~ r1_tarski(B_74,B_2)
      | ~ r1_tarski(B_73,B_74)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_541,plain,(
    ! [A_121,B_122,B_123] :
      ( r2_hidden('#skF_2'(A_121,B_122),u1_struct_0('#skF_4'))
      | ~ r1_tarski(B_122,u1_struct_0(B_123))
      | r1_xboole_0(A_121,B_122)
      | ~ m1_pre_topc(B_123,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_326,c_190])).

tff(c_547,plain,(
    ! [A_121,B_95] :
      ( r2_hidden('#skF_2'(A_121,u1_struct_0(B_95)),u1_struct_0('#skF_4'))
      | r1_xboole_0(A_121,u1_struct_0(B_95))
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ m1_pre_topc(B_95,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_307,c_541])).

tff(c_557,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_2'(A_124,u1_struct_0(B_125)),u1_struct_0('#skF_4'))
      | r1_xboole_0(A_124,u1_struct_0(B_125))
      | ~ m1_pre_topc(B_125,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_547])).

tff(c_196,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(u1_struct_0(A_80),u1_struct_0(B_81))
      | ~ r1_tsep_1(A_80,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_395,plain,(
    ! [C_102,B_103,A_104] :
      ( ~ r2_hidden(C_102,u1_struct_0(B_103))
      | ~ r2_hidden(C_102,u1_struct_0(A_104))
      | ~ r1_tsep_1(A_104,B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_196,c_8])).

tff(c_418,plain,(
    ! [A_6,B_103,A_104] :
      ( ~ r2_hidden('#skF_2'(A_6,u1_struct_0(B_103)),u1_struct_0(A_104))
      | ~ r1_tsep_1(A_104,B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0(A_104)
      | r1_xboole_0(A_6,u1_struct_0(B_103)) ) ),
    inference(resolution,[status(thm)],[c_10,c_395])).

tff(c_565,plain,(
    ! [B_125,A_124] :
      ( ~ r1_tsep_1('#skF_4',B_125)
      | ~ l1_struct_0(B_125)
      | ~ l1_struct_0('#skF_4')
      | r1_xboole_0(A_124,u1_struct_0(B_125))
      | ~ m1_pre_topc(B_125,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_557,c_418])).

tff(c_568,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_571,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_568])).

tff(c_575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_571])).

tff(c_577,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_79,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_67])).

tff(c_36,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_145,plain,(
    ! [B_65,A_66] :
      ( r1_tsep_1(B_65,A_66)
      | ~ r1_tsep_1(A_66,B_65)
      | ~ l1_struct_0(B_65)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_148,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_149,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_156,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_149])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_156])).

tff(c_161,plain,
    ( ~ l1_struct_0('#skF_6')
    | r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_163,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_166,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_166])).

tff(c_172,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_162,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_225,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_237,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_225])).

tff(c_130,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_142,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_130])).

tff(c_294,plain,(
    ! [B_95] :
      ( r1_tarski(u1_struct_0(B_95),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_237,c_290])).

tff(c_310,plain,(
    ! [B_95] :
      ( r1_tarski(u1_struct_0(B_95),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_294])).

tff(c_339,plain,(
    ! [B_99] :
      ( r1_tarski(u1_struct_0(B_99),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_99,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_294])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_191,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden('#skF_2'(A_75,B_76),B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_194,plain,(
    ! [A_75,B_76,B_2,B_77] :
      ( r2_hidden('#skF_2'(A_75,B_76),B_2)
      | ~ r1_tarski(B_77,B_2)
      | ~ r1_tarski(A_75,B_77)
      | r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_745,plain,(
    ! [A_157,B_158,B_159] :
      ( r2_hidden('#skF_2'(A_157,B_158),u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_157,u1_struct_0(B_159))
      | r1_xboole_0(A_157,B_158)
      | ~ m1_pre_topc(B_159,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_339,c_194])).

tff(c_752,plain,(
    ! [B_95,B_158] :
      ( r2_hidden('#skF_2'(u1_struct_0(B_95),B_158),u1_struct_0('#skF_5'))
      | r1_xboole_0(u1_struct_0(B_95),B_158)
      | ~ m1_pre_topc('#skF_5','#skF_5')
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_310,c_745])).

tff(c_768,plain,(
    ! [B_160,B_161] :
      ( r2_hidden('#skF_2'(u1_struct_0(B_160),B_161),u1_struct_0('#skF_5'))
      | r1_xboole_0(u1_struct_0(B_160),B_161)
      | ~ m1_pre_topc(B_160,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_752])).

tff(c_775,plain,(
    ! [B_103,B_160] :
      ( ~ r1_tsep_1('#skF_5',B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0('#skF_5')
      | r1_xboole_0(u1_struct_0(B_160),u1_struct_0(B_103))
      | ~ m1_pre_topc(B_160,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_768,c_418])).

tff(c_813,plain,(
    ! [B_168,B_169] :
      ( ~ r1_tsep_1('#skF_5',B_168)
      | ~ l1_struct_0(B_168)
      | r1_xboole_0(u1_struct_0(B_169),u1_struct_0(B_168))
      | ~ m1_pre_topc(B_169,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_775])).

tff(c_26,plain,(
    ! [A_20,B_22] :
      ( r1_tsep_1(A_20,B_22)
      | ~ r1_xboole_0(u1_struct_0(A_20),u1_struct_0(B_22))
      | ~ l1_struct_0(B_22)
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_827,plain,(
    ! [B_172,B_173] :
      ( r1_tsep_1(B_172,B_173)
      | ~ l1_struct_0(B_172)
      | ~ r1_tsep_1('#skF_5',B_173)
      | ~ l1_struct_0(B_173)
      | ~ m1_pre_topc(B_172,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_813,c_26])).

tff(c_829,plain,(
    ! [B_172] :
      ( r1_tsep_1(B_172,'#skF_6')
      | ~ l1_struct_0(B_172)
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_172,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_827])).

tff(c_833,plain,(
    ! [B_174] :
      ( r1_tsep_1(B_174,'#skF_6')
      | ~ l1_struct_0(B_174)
      | ~ m1_pre_topc(B_174,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_829])).

tff(c_38,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_63,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_862,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_833,c_63])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_577,c_862])).

tff(c_894,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_895,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_974,plain,(
    ! [B_195,A_196] :
      ( r1_tsep_1(B_195,A_196)
      | ~ r1_tsep_1(A_196,B_195)
      | ~ l1_struct_0(B_195)
      | ~ l1_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_976,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_895,c_974])).

tff(c_981,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_976])).

tff(c_985,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_981])).

tff(c_988,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_985])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_988])).

tff(c_993,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_981])).

tff(c_997,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_993])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_997])).

tff(c_1003,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1002,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1090,plain,(
    ! [B_217,A_218] :
      ( r1_tsep_1(B_217,A_218)
      | ~ r1_tsep_1(A_218,B_217)
      | ~ l1_struct_0(B_217)
      | ~ l1_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1092,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1002,c_1090])).

tff(c_1095,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_1092])).

tff(c_1096,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1095])).

tff(c_1099,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1096])).

tff(c_1103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1099])).

tff(c_1104,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1095])).

tff(c_1108,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1104])).

tff(c_1112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.50  
% 3.38/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.38/1.51  
% 3.38/1.51  %Foreground sorts:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Background operators:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Foreground operators:
% 3.38/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.38/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.38/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.38/1.51  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.38/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.38/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.51  
% 3.38/1.53  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.38/1.53  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.38/1.53  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.38/1.53  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.53  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.38/1.53  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.38/1.53  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.38/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.53  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.38/1.53  tff(f_93, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.38/1.53  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_1005, plain, (![B_197, A_198]: (l1_pre_topc(B_197) | ~m1_pre_topc(B_197, A_198) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.53  tff(c_1017, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1005])).
% 3.38/1.53  tff(c_1027, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1017])).
% 3.38/1.53  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.38/1.53  tff(c_42, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_1008, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1005])).
% 3.38/1.53  tff(c_1020, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1008])).
% 3.38/1.53  tff(c_896, plain, (![B_175, A_176]: (l1_pre_topc(B_175) | ~m1_pre_topc(B_175, A_176) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.53  tff(c_899, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_896])).
% 3.38/1.53  tff(c_911, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_899])).
% 3.38/1.53  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_902, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_896])).
% 3.38/1.53  tff(c_914, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_902])).
% 3.38/1.53  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_64, plain, (![B_45, A_46]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.53  tff(c_76, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_64])).
% 3.38/1.53  tff(c_86, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_76])).
% 3.38/1.53  tff(c_83, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_64])).
% 3.38/1.53  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_83])).
% 3.38/1.53  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.53  tff(c_212, plain, (![B_90, C_91, A_92]: (m1_pre_topc(B_90, C_91) | ~r1_tarski(u1_struct_0(B_90), u1_struct_0(C_91)) | ~m1_pre_topc(C_91, A_92) | ~m1_pre_topc(B_90, A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.38/1.53  tff(c_217, plain, (![B_93, A_94]: (m1_pre_topc(B_93, B_93) | ~m1_pre_topc(B_93, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(resolution, [status(thm)], [c_18, c_212])).
% 3.38/1.53  tff(c_221, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_217])).
% 3.38/1.53  tff(c_231, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_221])).
% 3.38/1.53  tff(c_118, plain, (![B_63, A_64]: (v2_pre_topc(B_63) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.53  tff(c_124, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_118])).
% 3.38/1.53  tff(c_136, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_124])).
% 3.38/1.53  tff(c_290, plain, (![B_95, C_96, A_97]: (r1_tarski(u1_struct_0(B_95), u1_struct_0(C_96)) | ~m1_pre_topc(B_95, C_96) | ~m1_pre_topc(C_96, A_97) | ~m1_pre_topc(B_95, A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.38/1.53  tff(c_292, plain, (![B_95]: (r1_tarski(u1_struct_0(B_95), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_95, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_231, c_290])).
% 3.38/1.53  tff(c_307, plain, (![B_95]: (r1_tarski(u1_struct_0(B_95), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_95, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_88, c_292])).
% 3.38/1.53  tff(c_326, plain, (![B_98]: (r1_tarski(u1_struct_0(B_98), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_98, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_88, c_292])).
% 3.38/1.53  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.53  tff(c_107, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.53  tff(c_187, plain, (![A_72, B_73, B_74]: (r2_hidden('#skF_2'(A_72, B_73), B_74) | ~r1_tarski(B_73, B_74) | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_10, c_107])).
% 3.38/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.53  tff(c_190, plain, (![A_72, B_73, B_2, B_74]: (r2_hidden('#skF_2'(A_72, B_73), B_2) | ~r1_tarski(B_74, B_2) | ~r1_tarski(B_73, B_74) | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_187, c_2])).
% 3.38/1.53  tff(c_541, plain, (![A_121, B_122, B_123]: (r2_hidden('#skF_2'(A_121, B_122), u1_struct_0('#skF_4')) | ~r1_tarski(B_122, u1_struct_0(B_123)) | r1_xboole_0(A_121, B_122) | ~m1_pre_topc(B_123, '#skF_4'))), inference(resolution, [status(thm)], [c_326, c_190])).
% 3.38/1.53  tff(c_547, plain, (![A_121, B_95]: (r2_hidden('#skF_2'(A_121, u1_struct_0(B_95)), u1_struct_0('#skF_4')) | r1_xboole_0(A_121, u1_struct_0(B_95)) | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc(B_95, '#skF_4'))), inference(resolution, [status(thm)], [c_307, c_541])).
% 3.38/1.53  tff(c_557, plain, (![A_124, B_125]: (r2_hidden('#skF_2'(A_124, u1_struct_0(B_125)), u1_struct_0('#skF_4')) | r1_xboole_0(A_124, u1_struct_0(B_125)) | ~m1_pre_topc(B_125, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_547])).
% 3.38/1.53  tff(c_196, plain, (![A_80, B_81]: (r1_xboole_0(u1_struct_0(A_80), u1_struct_0(B_81)) | ~r1_tsep_1(A_80, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.53  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.53  tff(c_395, plain, (![C_102, B_103, A_104]: (~r2_hidden(C_102, u1_struct_0(B_103)) | ~r2_hidden(C_102, u1_struct_0(A_104)) | ~r1_tsep_1(A_104, B_103) | ~l1_struct_0(B_103) | ~l1_struct_0(A_104))), inference(resolution, [status(thm)], [c_196, c_8])).
% 3.38/1.53  tff(c_418, plain, (![A_6, B_103, A_104]: (~r2_hidden('#skF_2'(A_6, u1_struct_0(B_103)), u1_struct_0(A_104)) | ~r1_tsep_1(A_104, B_103) | ~l1_struct_0(B_103) | ~l1_struct_0(A_104) | r1_xboole_0(A_6, u1_struct_0(B_103)))), inference(resolution, [status(thm)], [c_10, c_395])).
% 3.38/1.53  tff(c_565, plain, (![B_125, A_124]: (~r1_tsep_1('#skF_4', B_125) | ~l1_struct_0(B_125) | ~l1_struct_0('#skF_4') | r1_xboole_0(A_124, u1_struct_0(B_125)) | ~m1_pre_topc(B_125, '#skF_4'))), inference(resolution, [status(thm)], [c_557, c_418])).
% 3.38/1.53  tff(c_568, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_565])).
% 3.38/1.53  tff(c_571, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_568])).
% 3.38/1.53  tff(c_575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_571])).
% 3.38/1.53  tff(c_577, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_565])).
% 3.38/1.53  tff(c_67, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_64])).
% 3.38/1.53  tff(c_79, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_67])).
% 3.38/1.53  tff(c_36, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_62, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 3.38/1.53  tff(c_145, plain, (![B_65, A_66]: (r1_tsep_1(B_65, A_66) | ~r1_tsep_1(A_66, B_65) | ~l1_struct_0(B_65) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.53  tff(c_148, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_145])).
% 3.38/1.53  tff(c_149, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_148])).
% 3.38/1.53  tff(c_156, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_149])).
% 3.38/1.53  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_156])).
% 3.38/1.53  tff(c_161, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_148])).
% 3.38/1.53  tff(c_163, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_161])).
% 3.38/1.53  tff(c_166, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_22, c_163])).
% 3.38/1.53  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_166])).
% 3.38/1.53  tff(c_172, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_161])).
% 3.38/1.53  tff(c_162, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_148])).
% 3.38/1.53  tff(c_225, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_217])).
% 3.38/1.53  tff(c_237, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_225])).
% 3.38/1.53  tff(c_130, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_118])).
% 3.38/1.53  tff(c_142, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_130])).
% 3.38/1.53  tff(c_294, plain, (![B_95]: (r1_tarski(u1_struct_0(B_95), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_95, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_237, c_290])).
% 3.38/1.53  tff(c_310, plain, (![B_95]: (r1_tarski(u1_struct_0(B_95), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_95, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_294])).
% 3.38/1.53  tff(c_339, plain, (![B_99]: (r1_tarski(u1_struct_0(B_99), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_99, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_294])).
% 3.38/1.53  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.53  tff(c_191, plain, (![A_75, B_76, B_77]: (r2_hidden('#skF_2'(A_75, B_76), B_77) | ~r1_tarski(A_75, B_77) | r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_12, c_107])).
% 3.38/1.53  tff(c_194, plain, (![A_75, B_76, B_2, B_77]: (r2_hidden('#skF_2'(A_75, B_76), B_2) | ~r1_tarski(B_77, B_2) | ~r1_tarski(A_75, B_77) | r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_191, c_2])).
% 3.38/1.53  tff(c_745, plain, (![A_157, B_158, B_159]: (r2_hidden('#skF_2'(A_157, B_158), u1_struct_0('#skF_5')) | ~r1_tarski(A_157, u1_struct_0(B_159)) | r1_xboole_0(A_157, B_158) | ~m1_pre_topc(B_159, '#skF_5'))), inference(resolution, [status(thm)], [c_339, c_194])).
% 3.38/1.53  tff(c_752, plain, (![B_95, B_158]: (r2_hidden('#skF_2'(u1_struct_0(B_95), B_158), u1_struct_0('#skF_5')) | r1_xboole_0(u1_struct_0(B_95), B_158) | ~m1_pre_topc('#skF_5', '#skF_5') | ~m1_pre_topc(B_95, '#skF_5'))), inference(resolution, [status(thm)], [c_310, c_745])).
% 3.38/1.53  tff(c_768, plain, (![B_160, B_161]: (r2_hidden('#skF_2'(u1_struct_0(B_160), B_161), u1_struct_0('#skF_5')) | r1_xboole_0(u1_struct_0(B_160), B_161) | ~m1_pre_topc(B_160, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_752])).
% 3.38/1.53  tff(c_775, plain, (![B_103, B_160]: (~r1_tsep_1('#skF_5', B_103) | ~l1_struct_0(B_103) | ~l1_struct_0('#skF_5') | r1_xboole_0(u1_struct_0(B_160), u1_struct_0(B_103)) | ~m1_pre_topc(B_160, '#skF_5'))), inference(resolution, [status(thm)], [c_768, c_418])).
% 3.38/1.53  tff(c_813, plain, (![B_168, B_169]: (~r1_tsep_1('#skF_5', B_168) | ~l1_struct_0(B_168) | r1_xboole_0(u1_struct_0(B_169), u1_struct_0(B_168)) | ~m1_pre_topc(B_169, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_775])).
% 3.38/1.53  tff(c_26, plain, (![A_20, B_22]: (r1_tsep_1(A_20, B_22) | ~r1_xboole_0(u1_struct_0(A_20), u1_struct_0(B_22)) | ~l1_struct_0(B_22) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.53  tff(c_827, plain, (![B_172, B_173]: (r1_tsep_1(B_172, B_173) | ~l1_struct_0(B_172) | ~r1_tsep_1('#skF_5', B_173) | ~l1_struct_0(B_173) | ~m1_pre_topc(B_172, '#skF_5'))), inference(resolution, [status(thm)], [c_813, c_26])).
% 3.38/1.53  tff(c_829, plain, (![B_172]: (r1_tsep_1(B_172, '#skF_6') | ~l1_struct_0(B_172) | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_172, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_827])).
% 3.38/1.53  tff(c_833, plain, (![B_174]: (r1_tsep_1(B_174, '#skF_6') | ~l1_struct_0(B_174) | ~m1_pre_topc(B_174, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_829])).
% 3.38/1.53  tff(c_38, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.38/1.53  tff(c_63, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_38])).
% 3.38/1.53  tff(c_862, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_833, c_63])).
% 3.38/1.53  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_577, c_862])).
% 3.38/1.53  tff(c_894, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 3.38/1.53  tff(c_895, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 3.38/1.53  tff(c_974, plain, (![B_195, A_196]: (r1_tsep_1(B_195, A_196) | ~r1_tsep_1(A_196, B_195) | ~l1_struct_0(B_195) | ~l1_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.53  tff(c_976, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_895, c_974])).
% 3.38/1.53  tff(c_981, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_894, c_976])).
% 3.38/1.53  tff(c_985, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_981])).
% 3.38/1.53  tff(c_988, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_985])).
% 3.38/1.53  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_914, c_988])).
% 3.38/1.53  tff(c_993, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_981])).
% 3.38/1.53  tff(c_997, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_22, c_993])).
% 3.38/1.53  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_911, c_997])).
% 3.38/1.53  tff(c_1003, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 3.38/1.53  tff(c_1002, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 3.38/1.53  tff(c_1090, plain, (![B_217, A_218]: (r1_tsep_1(B_217, A_218) | ~r1_tsep_1(A_218, B_217) | ~l1_struct_0(B_217) | ~l1_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.53  tff(c_1092, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1002, c_1090])).
% 3.38/1.53  tff(c_1095, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1003, c_1092])).
% 3.38/1.53  tff(c_1096, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1095])).
% 3.38/1.53  tff(c_1099, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1096])).
% 3.38/1.53  tff(c_1103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1099])).
% 3.38/1.53  tff(c_1104, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1095])).
% 3.38/1.53  tff(c_1108, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1104])).
% 3.38/1.53  tff(c_1112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1108])).
% 3.38/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.53  
% 3.38/1.53  Inference rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Ref     : 0
% 3.38/1.53  #Sup     : 196
% 3.38/1.53  #Fact    : 0
% 3.38/1.53  #Define  : 0
% 3.38/1.53  #Split   : 13
% 3.38/1.53  #Chain   : 0
% 3.38/1.53  #Close   : 0
% 3.38/1.53  
% 3.38/1.53  Ordering : KBO
% 3.38/1.53  
% 3.38/1.53  Simplification rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Subsume      : 32
% 3.38/1.53  #Demod        : 155
% 3.38/1.53  #Tautology    : 36
% 3.38/1.53  #SimpNegUnit  : 2
% 3.38/1.53  #BackRed      : 0
% 3.38/1.53  
% 3.38/1.53  #Partial instantiations: 0
% 3.38/1.53  #Strategies tried      : 1
% 3.38/1.53  
% 3.38/1.53  Timing (in seconds)
% 3.38/1.53  ----------------------
% 3.38/1.53  Preprocessing        : 0.30
% 3.38/1.53  Parsing              : 0.17
% 3.38/1.53  CNF conversion       : 0.02
% 3.54/1.53  Main loop            : 0.43
% 3.54/1.53  Inferencing          : 0.16
% 3.54/1.53  Reduction            : 0.12
% 3.54/1.53  Demodulation         : 0.08
% 3.54/1.54  BG Simplification    : 0.02
% 3.54/1.54  Subsumption          : 0.09
% 3.54/1.54  Abstraction          : 0.02
% 3.54/1.54  MUC search           : 0.00
% 3.54/1.54  Cooper               : 0.00
% 3.54/1.54  Total                : 0.78
% 3.54/1.54  Index Insertion      : 0.00
% 3.54/1.54  Index Deletion       : 0.00
% 3.54/1.54  Index Matching       : 0.00
% 3.54/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
