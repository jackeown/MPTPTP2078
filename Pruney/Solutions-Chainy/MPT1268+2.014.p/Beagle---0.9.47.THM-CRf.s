%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 153 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 424 expanded)
%              Number of equality atoms :   23 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_79,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_439,plain,(
    ! [B_103,A_104] :
      ( v2_tops_1(B_103,A_104)
      | k1_tops_1(A_104,B_103) != k1_xboole_0
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_446,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_439])).

tff(c_454,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_446])).

tff(c_455,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_454])).

tff(c_269,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_tops_1(A_90,B_91),B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_274,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_269])).

tff(c_281,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_274])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_349,plain,(
    ! [A_94,B_95] :
      ( v3_pre_topc(k1_tops_1(A_94,B_95),A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_354,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_349])).

tff(c_361,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_354])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_191,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_211,plain,(
    ! [A_80] :
      ( r1_tarski(A_80,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_191])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_219,plain,(
    ! [A_8,A_80] :
      ( r1_tarski(A_8,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_8,A_80)
      | ~ r1_tarski(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_211,c_14])).

tff(c_284,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_281,c_219])).

tff(c_296,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_284])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    ! [C_43] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_43
      | ~ v3_pre_topc(C_43,'#skF_2')
      | ~ r1_tarski(C_43,'#skF_3')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_159,plain,(
    ! [C_71] :
      ( k1_xboole_0 = C_71
      | ~ v3_pre_topc(C_71,'#skF_2')
      | ~ r1_tarski(C_71,'#skF_3')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_64])).

tff(c_472,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | ~ v3_pre_topc(A_105,'#skF_2')
      | ~ r1_tarski(A_105,'#skF_3')
      | ~ r1_tarski(A_105,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_483,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_296,c_472])).

tff(c_504,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_361,c_483])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_504])).

tff(c_507,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_562,plain,(
    ! [B_116,A_117] :
      ( ~ r1_xboole_0(B_116,A_117)
      | ~ r1_tarski(B_116,A_117)
      | v1_xboole_0(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_567,plain,(
    ! [A_118] :
      ( ~ r1_tarski(A_118,k1_xboole_0)
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_16,c_562])).

tff(c_572,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_567])).

tff(c_508,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_512,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_48])).

tff(c_50,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_510,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_50])).

tff(c_52,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_529,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_52])).

tff(c_946,plain,(
    ! [A_157,B_158] :
      ( k1_tops_1(A_157,B_158) = k1_xboole_0
      | ~ v2_tops_1(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_956,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_946])).

tff(c_968,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_508,c_956])).

tff(c_1184,plain,(
    ! [B_166,A_167,C_168] :
      ( r1_tarski(B_166,k1_tops_1(A_167,C_168))
      | ~ r1_tarski(B_166,C_168)
      | ~ v3_pre_topc(B_166,A_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1191,plain,(
    ! [B_166] :
      ( r1_tarski(B_166,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_166,'#skF_3')
      | ~ v3_pre_topc(B_166,'#skF_2')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1184])).

tff(c_1220,plain,(
    ! [B_171] :
      ( r1_tarski(B_171,k1_xboole_0)
      | ~ r1_tarski(B_171,'#skF_3')
      | ~ v3_pre_topc(B_171,'#skF_2')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_968,c_1191])).

tff(c_1223,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_529,c_1220])).

tff(c_1237,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_510,c_1223])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k2_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_573,plain,(
    ! [C_119,B_120,A_121] :
      ( ~ v1_xboole_0(C_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(C_119))
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_586,plain,(
    ! [A_122,A_123] :
      ( ~ v1_xboole_0(A_122)
      | ~ r2_hidden(A_123,A_122) ) ),
    inference(resolution,[status(thm)],[c_65,c_573])).

tff(c_604,plain,(
    ! [A_127,B_128] :
      ( ~ v1_xboole_0(A_127)
      | r1_tarski(A_127,B_128) ) ),
    inference(resolution,[status(thm)],[c_6,c_586])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_627,plain,(
    ! [B_128,A_127] :
      ( B_128 = A_127
      | ~ r1_tarski(B_128,A_127)
      | ~ v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_604,c_8])).

tff(c_1256,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1237,c_627])).

tff(c_1276,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_1256])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_1276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.50  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.16/1.50  
% 3.16/1.50  %Foreground sorts:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Background operators:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Foreground operators:
% 3.16/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.50  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.16/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.16/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.16/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.16/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.16/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.50  
% 3.16/1.51  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.16/1.51  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.16/1.51  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.16/1.51  tff(f_77, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.16/1.51  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.51  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.51  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.16/1.51  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/1.51  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.16/1.51  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.16/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.51  tff(f_56, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.16/1.51  tff(f_58, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.16/1.51  tff(f_69, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.16/1.51  tff(c_46, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_79, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 3.16/1.51  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_439, plain, (![B_103, A_104]: (v2_tops_1(B_103, A_104) | k1_tops_1(A_104, B_103)!=k1_xboole_0 | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.16/1.51  tff(c_446, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_439])).
% 3.16/1.51  tff(c_454, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_446])).
% 3.16/1.51  tff(c_455, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_79, c_454])).
% 3.16/1.51  tff(c_269, plain, (![A_90, B_91]: (r1_tarski(k1_tops_1(A_90, B_91), B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.51  tff(c_274, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_269])).
% 3.16/1.51  tff(c_281, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_274])).
% 3.16/1.51  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_349, plain, (![A_94, B_95]: (v3_pre_topc(k1_tops_1(A_94, B_95), A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.51  tff(c_354, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_349])).
% 3.16/1.51  tff(c_361, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_354])).
% 3.16/1.51  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.51  tff(c_81, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.51  tff(c_92, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_81])).
% 3.16/1.51  tff(c_191, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.51  tff(c_211, plain, (![A_80]: (r1_tarski(A_80, u1_struct_0('#skF_2')) | ~r1_tarski(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_92, c_191])).
% 3.16/1.51  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.51  tff(c_219, plain, (![A_8, A_80]: (r1_tarski(A_8, u1_struct_0('#skF_2')) | ~r1_tarski(A_8, A_80) | ~r1_tarski(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_211, c_14])).
% 3.16/1.51  tff(c_284, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_281, c_219])).
% 3.16/1.51  tff(c_296, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_284])).
% 3.16/1.51  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.51  tff(c_64, plain, (![C_43]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_43 | ~v3_pre_topc(C_43, '#skF_2') | ~r1_tarski(C_43, '#skF_3') | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_159, plain, (![C_71]: (k1_xboole_0=C_71 | ~v3_pre_topc(C_71, '#skF_2') | ~r1_tarski(C_71, '#skF_3') | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_79, c_64])).
% 3.16/1.51  tff(c_472, plain, (![A_105]: (k1_xboole_0=A_105 | ~v3_pre_topc(A_105, '#skF_2') | ~r1_tarski(A_105, '#skF_3') | ~r1_tarski(A_105, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_26, c_159])).
% 3.16/1.51  tff(c_483, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_296, c_472])).
% 3.16/1.51  tff(c_504, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_281, c_361, c_483])).
% 3.16/1.51  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455, c_504])).
% 3.16/1.51  tff(c_507, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 3.16/1.51  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.16/1.51  tff(c_562, plain, (![B_116, A_117]: (~r1_xboole_0(B_116, A_117) | ~r1_tarski(B_116, A_117) | v1_xboole_0(B_116))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.51  tff(c_567, plain, (![A_118]: (~r1_tarski(A_118, k1_xboole_0) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_16, c_562])).
% 3.16/1.51  tff(c_572, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_567])).
% 3.16/1.51  tff(c_508, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.16/1.51  tff(c_48, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_512, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_48])).
% 3.16/1.51  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_510, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_50])).
% 3.16/1.51  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.16/1.51  tff(c_529, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_52])).
% 3.16/1.51  tff(c_946, plain, (![A_157, B_158]: (k1_tops_1(A_157, B_158)=k1_xboole_0 | ~v2_tops_1(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.16/1.51  tff(c_956, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_946])).
% 3.16/1.51  tff(c_968, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_508, c_956])).
% 3.16/1.51  tff(c_1184, plain, (![B_166, A_167, C_168]: (r1_tarski(B_166, k1_tops_1(A_167, C_168)) | ~r1_tarski(B_166, C_168) | ~v3_pre_topc(B_166, A_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.16/1.51  tff(c_1191, plain, (![B_166]: (r1_tarski(B_166, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_166, '#skF_3') | ~v3_pre_topc(B_166, '#skF_2') | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1184])).
% 3.16/1.51  tff(c_1220, plain, (![B_171]: (r1_tarski(B_171, k1_xboole_0) | ~r1_tarski(B_171, '#skF_3') | ~v3_pre_topc(B_171, '#skF_2') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_968, c_1191])).
% 3.16/1.51  tff(c_1223, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_529, c_1220])).
% 3.16/1.51  tff(c_1237, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_510, c_1223])).
% 3.16/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.51  tff(c_20, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.51  tff(c_22, plain, (![A_15]: (m1_subset_1(k2_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.51  tff(c_65, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.16/1.51  tff(c_573, plain, (![C_119, B_120, A_121]: (~v1_xboole_0(C_119) | ~m1_subset_1(B_120, k1_zfmisc_1(C_119)) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.51  tff(c_586, plain, (![A_122, A_123]: (~v1_xboole_0(A_122) | ~r2_hidden(A_123, A_122))), inference(resolution, [status(thm)], [c_65, c_573])).
% 3.16/1.51  tff(c_604, plain, (![A_127, B_128]: (~v1_xboole_0(A_127) | r1_tarski(A_127, B_128))), inference(resolution, [status(thm)], [c_6, c_586])).
% 3.16/1.51  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.51  tff(c_627, plain, (![B_128, A_127]: (B_128=A_127 | ~r1_tarski(B_128, A_127) | ~v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_604, c_8])).
% 3.16/1.51  tff(c_1256, plain, (k1_xboole_0='#skF_4' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1237, c_627])).
% 3.16/1.51  tff(c_1276, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_572, c_1256])).
% 3.16/1.51  tff(c_1278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_507, c_1276])).
% 3.16/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  Inference rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Ref     : 0
% 3.16/1.51  #Sup     : 275
% 3.16/1.51  #Fact    : 0
% 3.16/1.51  #Define  : 0
% 3.16/1.51  #Split   : 15
% 3.16/1.51  #Chain   : 0
% 3.16/1.51  #Close   : 0
% 3.16/1.51  
% 3.16/1.51  Ordering : KBO
% 3.16/1.51  
% 3.16/1.51  Simplification rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Subsume      : 113
% 3.16/1.51  #Demod        : 91
% 3.16/1.51  #Tautology    : 44
% 3.16/1.51  #SimpNegUnit  : 7
% 3.16/1.51  #BackRed      : 3
% 3.16/1.51  
% 3.16/1.51  #Partial instantiations: 0
% 3.16/1.51  #Strategies tried      : 1
% 3.16/1.51  
% 3.16/1.51  Timing (in seconds)
% 3.16/1.51  ----------------------
% 3.16/1.52  Preprocessing        : 0.32
% 3.16/1.52  Parsing              : 0.17
% 3.16/1.52  CNF conversion       : 0.02
% 3.16/1.52  Main loop            : 0.42
% 3.16/1.52  Inferencing          : 0.14
% 3.16/1.52  Reduction            : 0.13
% 3.16/1.52  Demodulation         : 0.09
% 3.16/1.52  BG Simplification    : 0.02
% 3.16/1.52  Subsumption          : 0.10
% 3.16/1.52  Abstraction          : 0.02
% 3.16/1.52  MUC search           : 0.00
% 3.16/1.52  Cooper               : 0.00
% 3.16/1.52  Total                : 0.78
% 3.16/1.52  Index Insertion      : 0.00
% 3.16/1.52  Index Deletion       : 0.00
% 3.16/1.52  Index Matching       : 0.00
% 3.16/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
