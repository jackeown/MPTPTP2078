%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 5.01s
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
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2233,plain,(
    ! [B_239,A_240] :
      ( l1_pre_topc(B_239)
      | ~ m1_pre_topc(B_239,A_240)
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2236,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2233])).

tff(c_2248,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2236])).

tff(c_36,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2239,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2233])).

tff(c_2251,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2239])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2109,plain,(
    ! [B_212,A_213] :
      ( l1_pre_topc(B_212)
      | ~ m1_pre_topc(B_212,A_213)
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2121,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2109])).

tff(c_2131,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2121])).

tff(c_2112,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2109])).

tff(c_2124,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2112])).

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

tff(c_167,plain,(
    ! [B_70,A_71] :
      ( r1_tsep_1(B_70,A_71)
      | ~ r1_tsep_1(A_71,B_70)
      | ~ l1_struct_0(B_70)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_170,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_77,c_167])).

tff(c_171,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_174,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_174])).

tff(c_179,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_181,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_181])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_206])).

tff(c_212,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_180,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_139,plain,(
    ! [B_65,A_66] :
      ( v2_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_151,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_139])).

tff(c_163,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_151])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_287,plain,(
    ! [B_94,C_95,A_96] :
      ( m1_pre_topc(B_94,C_95)
      | ~ r1_tarski(u1_struct_0(B_94),u1_struct_0(C_95))
      | ~ m1_pre_topc(C_95,A_96)
      | ~ m1_pre_topc(B_94,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_292,plain,(
    ! [B_97,A_98] :
      ( m1_pre_topc(B_97,B_97)
      | ~ m1_pre_topc(B_97,A_98)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_30,c_287])).

tff(c_300,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_292])).

tff(c_312,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_300])).

tff(c_365,plain,(
    ! [B_99,C_100,A_101] :
      ( r1_tarski(u1_struct_0(B_99),u1_struct_0(C_100))
      | ~ m1_pre_topc(B_99,C_100)
      | ~ m1_pre_topc(C_100,A_101)
      | ~ m1_pre_topc(B_99,A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_367,plain,(
    ! [B_99] :
      ( r1_tarski(u1_struct_0(B_99),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_99,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_312,c_365])).

tff(c_401,plain,(
    ! [B_102] :
      ( r1_tarski(u1_struct_0(B_102),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_102,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_114,c_367])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_527,plain,(
    ! [B_109] :
      ( k2_xboole_0(u1_struct_0(B_109),u1_struct_0('#skF_6')) = u1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_109,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_401,c_32])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_690,plain,(
    ! [D_116,B_117] :
      ( ~ r2_hidden(D_116,u1_struct_0(B_117))
      | r2_hidden(D_116,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_117,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_6])).

tff(c_717,plain,(
    ! [B_117,B_8] :
      ( r2_hidden('#skF_3'(u1_struct_0(B_117),B_8),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_117,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_117),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_690])).

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

tff(c_249,plain,(
    ! [C_82,B_83,A_84] :
      ( ~ r2_hidden(C_82,u1_struct_0(B_83))
      | ~ r2_hidden(C_82,u1_struct_0(A_84))
      | ~ r1_tsep_1(A_84,B_83)
      | ~ l1_struct_0(B_83)
      | ~ l1_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_241,c_20])).

tff(c_1896,plain,(
    ! [A_186,B_187,A_188] :
      ( ~ r2_hidden('#skF_3'(A_186,u1_struct_0(B_187)),u1_struct_0(A_188))
      | ~ r1_tsep_1(A_188,B_187)
      | ~ l1_struct_0(B_187)
      | ~ l1_struct_0(A_188)
      | r1_xboole_0(A_186,u1_struct_0(B_187)) ) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_1929,plain,(
    ! [B_187,B_117] :
      ( ~ r1_tsep_1('#skF_6',B_187)
      | ~ l1_struct_0(B_187)
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_117,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_117),u1_struct_0(B_187)) ) ),
    inference(resolution,[status(thm)],[c_717,c_1896])).

tff(c_2034,plain,(
    ! [B_201,B_202] :
      ( ~ r1_tsep_1('#skF_6',B_201)
      | ~ l1_struct_0(B_201)
      | ~ m1_pre_topc(B_202,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_202),u1_struct_0(B_201)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_1929])).

tff(c_40,plain,(
    ! [A_23,B_25] :
      ( r1_tsep_1(A_23,B_25)
      | ~ r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2070,plain,(
    ! [B_209,B_210] :
      ( r1_tsep_1(B_209,B_210)
      | ~ l1_struct_0(B_209)
      | ~ r1_tsep_1('#skF_6',B_210)
      | ~ l1_struct_0(B_210)
      | ~ m1_pre_topc(B_209,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2034,c_40])).

tff(c_2072,plain,(
    ! [B_209] :
      ( r1_tsep_1(B_209,'#skF_7')
      | ~ l1_struct_0(B_209)
      | ~ l1_struct_0('#skF_7')
      | ~ m1_pre_topc(B_209,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_77,c_2070])).

tff(c_2076,plain,(
    ! [B_211] :
      ( r1_tsep_1(B_211,'#skF_7')
      | ~ l1_struct_0(B_211)
      | ~ m1_pre_topc(B_211,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_2072])).

tff(c_52,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2087,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2076,c_76])).

tff(c_2099,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2087])).

tff(c_2102,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2099])).

tff(c_2106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2102])).

tff(c_2108,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2107,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2193,plain,(
    ! [B_234,A_235] :
      ( r1_tsep_1(B_234,A_235)
      | ~ r1_tsep_1(A_235,B_234)
      | ~ l1_struct_0(B_234)
      | ~ l1_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2195,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2107,c_2193])).

tff(c_2198,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2108,c_2195])).

tff(c_2199,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2198])).

tff(c_2202,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2199])).

tff(c_2206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_2202])).

tff(c_2207,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2198])).

tff(c_2211,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2207])).

tff(c_2215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2211])).

tff(c_2216,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2217,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2303,plain,(
    ! [B_258,A_259] :
      ( r1_tsep_1(B_258,A_259)
      | ~ r1_tsep_1(A_259,B_258)
      | ~ l1_struct_0(B_258)
      | ~ l1_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2307,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2217,c_2303])).

tff(c_2311,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2216,c_2307])).

tff(c_2312,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2311])).

tff(c_2316,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2312])).

tff(c_2320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_2316])).

tff(c_2321,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2311])).

tff(c_2325,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2321])).

tff(c_2329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_2325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.91  
% 5.01/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.91  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.01/1.91  
% 5.01/1.91  %Foreground sorts:
% 5.01/1.91  
% 5.01/1.91  
% 5.01/1.91  %Background operators:
% 5.01/1.91  
% 5.01/1.91  
% 5.01/1.91  %Foreground operators:
% 5.01/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.01/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.01/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.01/1.91  tff('#skF_7', type, '#skF_7': $i).
% 5.01/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.01/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.91  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.91  tff('#skF_6', type, '#skF_6': $i).
% 5.01/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.01/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.01/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.01/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.91  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.01/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.01/1.91  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 5.01/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.01/1.91  
% 5.01/1.94  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 5.01/1.94  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.01/1.94  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.01/1.94  tff(f_99, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 5.01/1.94  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.01/1.94  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.01/1.94  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.01/1.94  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.01/1.94  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.01/1.94  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.01/1.94  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 5.01/1.94  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_2233, plain, (![B_239, A_240]: (l1_pre_topc(B_239) | ~m1_pre_topc(B_239, A_240) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.01/1.94  tff(c_2236, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2233])).
% 5.01/1.94  tff(c_2248, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2236])).
% 5.01/1.94  tff(c_36, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.01/1.94  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_2239, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2233])).
% 5.01/1.94  tff(c_2251, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2239])).
% 5.01/1.94  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_2109, plain, (![B_212, A_213]: (l1_pre_topc(B_212) | ~m1_pre_topc(B_212, A_213) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.01/1.94  tff(c_2121, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2109])).
% 5.01/1.94  tff(c_2131, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2121])).
% 5.01/1.94  tff(c_2112, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2109])).
% 5.01/1.94  tff(c_2124, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2112])).
% 5.01/1.94  tff(c_92, plain, (![B_51, A_52]: (l1_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.01/1.94  tff(c_104, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_92])).
% 5.01/1.94  tff(c_114, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104])).
% 5.01/1.94  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_111, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_54, c_92])).
% 5.01/1.94  tff(c_115, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_111])).
% 5.01/1.94  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_115])).
% 5.01/1.94  tff(c_118, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 5.01/1.94  tff(c_95, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_92])).
% 5.01/1.94  tff(c_107, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_95])).
% 5.01/1.94  tff(c_50, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_77, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 5.01/1.94  tff(c_167, plain, (![B_70, A_71]: (r1_tsep_1(B_70, A_71) | ~r1_tsep_1(A_71, B_70) | ~l1_struct_0(B_70) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.01/1.94  tff(c_170, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_77, c_167])).
% 5.01/1.94  tff(c_171, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_170])).
% 5.01/1.94  tff(c_174, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_171])).
% 5.01/1.94  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_174])).
% 5.01/1.94  tff(c_179, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_170])).
% 5.01/1.94  tff(c_181, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_179])).
% 5.01/1.94  tff(c_206, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_181])).
% 5.01/1.94  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_206])).
% 5.01/1.94  tff(c_212, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_179])).
% 5.01/1.94  tff(c_180, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_170])).
% 5.01/1.94  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.01/1.94  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_139, plain, (![B_65, A_66]: (v2_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.01/1.94  tff(c_151, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_139])).
% 5.01/1.94  tff(c_163, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_151])).
% 5.01/1.94  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.01/1.94  tff(c_287, plain, (![B_94, C_95, A_96]: (m1_pre_topc(B_94, C_95) | ~r1_tarski(u1_struct_0(B_94), u1_struct_0(C_95)) | ~m1_pre_topc(C_95, A_96) | ~m1_pre_topc(B_94, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.01/1.94  tff(c_292, plain, (![B_97, A_98]: (m1_pre_topc(B_97, B_97) | ~m1_pre_topc(B_97, A_98) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(resolution, [status(thm)], [c_30, c_287])).
% 5.01/1.94  tff(c_300, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_292])).
% 5.01/1.94  tff(c_312, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_300])).
% 5.01/1.94  tff(c_365, plain, (![B_99, C_100, A_101]: (r1_tarski(u1_struct_0(B_99), u1_struct_0(C_100)) | ~m1_pre_topc(B_99, C_100) | ~m1_pre_topc(C_100, A_101) | ~m1_pre_topc(B_99, A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.01/1.94  tff(c_367, plain, (![B_99]: (r1_tarski(u1_struct_0(B_99), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_99, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_312, c_365])).
% 5.01/1.94  tff(c_401, plain, (![B_102]: (r1_tarski(u1_struct_0(B_102), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_102, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_114, c_367])).
% 5.01/1.94  tff(c_32, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.01/1.94  tff(c_527, plain, (![B_109]: (k2_xboole_0(u1_struct_0(B_109), u1_struct_0('#skF_6'))=u1_struct_0('#skF_6') | ~m1_pre_topc(B_109, '#skF_6'))), inference(resolution, [status(thm)], [c_401, c_32])).
% 5.01/1.94  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.01/1.94  tff(c_690, plain, (![D_116, B_117]: (~r2_hidden(D_116, u1_struct_0(B_117)) | r2_hidden(D_116, u1_struct_0('#skF_6')) | ~m1_pre_topc(B_117, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_527, c_6])).
% 5.01/1.94  tff(c_717, plain, (![B_117, B_8]: (r2_hidden('#skF_3'(u1_struct_0(B_117), B_8), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_117, '#skF_6') | r1_xboole_0(u1_struct_0(B_117), B_8))), inference(resolution, [status(thm)], [c_24, c_690])).
% 5.01/1.94  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.01/1.94  tff(c_241, plain, (![A_80, B_81]: (r1_xboole_0(u1_struct_0(A_80), u1_struct_0(B_81)) | ~r1_tsep_1(A_80, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.01/1.94  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.01/1.94  tff(c_249, plain, (![C_82, B_83, A_84]: (~r2_hidden(C_82, u1_struct_0(B_83)) | ~r2_hidden(C_82, u1_struct_0(A_84)) | ~r1_tsep_1(A_84, B_83) | ~l1_struct_0(B_83) | ~l1_struct_0(A_84))), inference(resolution, [status(thm)], [c_241, c_20])).
% 5.01/1.94  tff(c_1896, plain, (![A_186, B_187, A_188]: (~r2_hidden('#skF_3'(A_186, u1_struct_0(B_187)), u1_struct_0(A_188)) | ~r1_tsep_1(A_188, B_187) | ~l1_struct_0(B_187) | ~l1_struct_0(A_188) | r1_xboole_0(A_186, u1_struct_0(B_187)))), inference(resolution, [status(thm)], [c_22, c_249])).
% 5.01/1.94  tff(c_1929, plain, (![B_187, B_117]: (~r1_tsep_1('#skF_6', B_187) | ~l1_struct_0(B_187) | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_117, '#skF_6') | r1_xboole_0(u1_struct_0(B_117), u1_struct_0(B_187)))), inference(resolution, [status(thm)], [c_717, c_1896])).
% 5.01/1.94  tff(c_2034, plain, (![B_201, B_202]: (~r1_tsep_1('#skF_6', B_201) | ~l1_struct_0(B_201) | ~m1_pre_topc(B_202, '#skF_6') | r1_xboole_0(u1_struct_0(B_202), u1_struct_0(B_201)))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_1929])).
% 5.01/1.94  tff(c_40, plain, (![A_23, B_25]: (r1_tsep_1(A_23, B_25) | ~r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.01/1.94  tff(c_2070, plain, (![B_209, B_210]: (r1_tsep_1(B_209, B_210) | ~l1_struct_0(B_209) | ~r1_tsep_1('#skF_6', B_210) | ~l1_struct_0(B_210) | ~m1_pre_topc(B_209, '#skF_6'))), inference(resolution, [status(thm)], [c_2034, c_40])).
% 5.01/1.94  tff(c_2072, plain, (![B_209]: (r1_tsep_1(B_209, '#skF_7') | ~l1_struct_0(B_209) | ~l1_struct_0('#skF_7') | ~m1_pre_topc(B_209, '#skF_6'))), inference(resolution, [status(thm)], [c_77, c_2070])).
% 5.01/1.94  tff(c_2076, plain, (![B_211]: (r1_tsep_1(B_211, '#skF_7') | ~l1_struct_0(B_211) | ~m1_pre_topc(B_211, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_2072])).
% 5.01/1.94  tff(c_52, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.01/1.94  tff(c_76, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 5.01/1.94  tff(c_2087, plain, (~l1_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2076, c_76])).
% 5.01/1.94  tff(c_2099, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2087])).
% 5.01/1.94  tff(c_2102, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2099])).
% 5.01/1.94  tff(c_2106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_2102])).
% 5.01/1.94  tff(c_2108, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 5.01/1.94  tff(c_2107, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 5.01/1.94  tff(c_2193, plain, (![B_234, A_235]: (r1_tsep_1(B_234, A_235) | ~r1_tsep_1(A_235, B_234) | ~l1_struct_0(B_234) | ~l1_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.01/1.94  tff(c_2195, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2107, c_2193])).
% 5.01/1.94  tff(c_2198, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2108, c_2195])).
% 5.01/1.94  tff(c_2199, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_2198])).
% 5.01/1.94  tff(c_2202, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_2199])).
% 5.01/1.94  tff(c_2206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2124, c_2202])).
% 5.01/1.94  tff(c_2207, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_2198])).
% 5.01/1.94  tff(c_2211, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2207])).
% 5.01/1.94  tff(c_2215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2211])).
% 5.01/1.94  tff(c_2216, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 5.01/1.94  tff(c_2217, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 5.01/1.94  tff(c_2303, plain, (![B_258, A_259]: (r1_tsep_1(B_258, A_259) | ~r1_tsep_1(A_259, B_258) | ~l1_struct_0(B_258) | ~l1_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.01/1.94  tff(c_2307, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2217, c_2303])).
% 5.01/1.94  tff(c_2311, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2216, c_2307])).
% 5.01/1.94  tff(c_2312, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2311])).
% 5.01/1.94  tff(c_2316, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2312])).
% 5.01/1.94  tff(c_2320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2251, c_2316])).
% 5.01/1.94  tff(c_2321, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_2311])).
% 5.01/1.94  tff(c_2325, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_36, c_2321])).
% 5.01/1.94  tff(c_2329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2248, c_2325])).
% 5.01/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.94  
% 5.01/1.94  Inference rules
% 5.01/1.94  ----------------------
% 5.01/1.94  #Ref     : 0
% 5.01/1.94  #Sup     : 453
% 5.01/1.94  #Fact    : 10
% 5.01/1.94  #Define  : 0
% 5.01/1.94  #Split   : 14
% 5.01/1.94  #Chain   : 0
% 5.01/1.94  #Close   : 0
% 5.01/1.94  
% 5.01/1.94  Ordering : KBO
% 5.01/1.94  
% 5.01/1.94  Simplification rules
% 5.01/1.94  ----------------------
% 5.01/1.94  #Subsume      : 82
% 5.01/1.94  #Demod        : 220
% 5.01/1.94  #Tautology    : 96
% 5.01/1.94  #SimpNegUnit  : 2
% 5.01/1.94  #BackRed      : 0
% 5.01/1.94  
% 5.01/1.94  #Partial instantiations: 0
% 5.01/1.94  #Strategies tried      : 1
% 5.01/1.94  
% 5.01/1.94  Timing (in seconds)
% 5.01/1.94  ----------------------
% 5.01/1.94  Preprocessing        : 0.33
% 5.01/1.94  Parsing              : 0.19
% 5.01/1.94  CNF conversion       : 0.03
% 5.01/1.94  Main loop            : 0.78
% 5.01/1.94  Inferencing          : 0.29
% 5.01/1.94  Reduction            : 0.21
% 5.01/1.94  Demodulation         : 0.14
% 5.01/1.94  BG Simplification    : 0.04
% 5.01/1.94  Subsumption          : 0.18
% 5.01/1.94  Abstraction          : 0.03
% 5.01/1.94  MUC search           : 0.00
% 5.01/1.94  Cooper               : 0.00
% 5.01/1.94  Total                : 1.17
% 5.01/1.94  Index Insertion      : 0.00
% 5.01/1.94  Index Deletion       : 0.00
% 5.01/1.94  Index Matching       : 0.00
% 5.01/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
