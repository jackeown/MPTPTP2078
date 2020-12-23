%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 253 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 764 expanded)
%              Number of equality atoms :   37 ( 108 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_187,plain,(
    ! [B_102,A_103] :
      ( v2_tops_1(B_102,A_103)
      | k1_tops_1(A_103,B_102) != k1_xboole_0
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_194,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_187])).

tff(c_198,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_194])).

tff(c_199,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_198])).

tff(c_117,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_122,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_126,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_284,plain,(
    ! [A_116,B_117] :
      ( v3_pre_topc(k1_tops_1(A_116,B_117),A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_289,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_284])).

tff(c_293,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_289])).

tff(c_73,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_73])).

tff(c_82,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_74,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_82])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [C_64] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_64
      | ~ v3_pre_topc(C_64,'#skF_2')
      | ~ r1_tarski(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_325,plain,(
    ! [C_121] :
      ( k1_xboole_0 = C_121
      | ~ v3_pre_topc(C_121,'#skF_2')
      | ~ r1_tarski(C_121,'#skF_3')
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56])).

tff(c_340,plain,(
    ! [A_123] :
      ( k1_xboole_0 = A_123
      | ~ v3_pre_topc(A_123,'#skF_2')
      | ~ r1_tarski(A_123,'#skF_3')
      | ~ r1_tarski(A_123,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_325])).

tff(c_367,plain,(
    ! [A_124] :
      ( k1_xboole_0 = A_124
      | ~ v3_pre_topc(A_124,'#skF_2')
      | ~ r1_tarski(A_124,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_87,c_340])).

tff(c_370,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_293,c_367])).

tff(c_376,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_370])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_376])).

tff(c_379,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_380,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_385,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_40])).

tff(c_44,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_387,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_44])).

tff(c_612,plain,(
    ! [A_165,B_166] :
      ( k1_tops_1(A_165,B_166) = k1_xboole_0
      | ~ v2_tops_1(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_619,plain,
    ( k1_tops_1('#skF_2','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_612])).

tff(c_626,plain,
    ( k1_tops_1('#skF_2','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_619])).

tff(c_637,plain,(
    ~ v2_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_825,plain,(
    ! [B_186,A_187] :
      ( v2_tops_1(B_186,A_187)
      | k1_tops_1(A_187,B_186) != k1_xboole_0
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_832,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_825])).

tff(c_839,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_832])).

tff(c_840,plain,(
    k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_839])).

tff(c_42,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_383,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_42])).

tff(c_622,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_612])).

tff(c_629,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_380,c_622])).

tff(c_979,plain,(
    ! [A_197,B_198,C_199] :
      ( r1_tarski(k1_tops_1(A_197,B_198),k1_tops_1(A_197,C_199))
      | ~ r1_tarski(B_198,C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1010,plain,(
    ! [B_198] :
      ( r1_tarski(k1_tops_1('#skF_2',B_198),k1_xboole_0)
      | ~ r1_tarski(B_198,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_979])).

tff(c_1030,plain,(
    ! [B_200] :
      ( r1_tarski(k1_tops_1('#skF_2',B_200),k1_xboole_0)
      | ~ r1_tarski(B_200,'#skF_3')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1010])).

tff(c_1037,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_387,c_1030])).

tff(c_1044,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_1037])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_414,plain,(
    ! [A_133,C_134,B_135] :
      ( r1_tarski(A_133,C_134)
      | ~ r1_tarski(B_135,C_134)
      | ~ r1_tarski(A_133,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_426,plain,(
    ! [A_133,A_4] :
      ( r1_tarski(A_133,A_4)
      | ~ r1_tarski(A_133,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_414])).

tff(c_1088,plain,(
    ! [A_201] : r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_201) ),
    inference(resolution,[status(thm)],[c_1044,c_426])).

tff(c_12,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_388,plain,(
    ! [B_126,A_127] :
      ( ~ r1_tarski(B_126,A_127)
      | ~ r2_hidden(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_392,plain,(
    ! [A_9] :
      ( ~ r1_tarski(A_9,'#skF_1'(A_9))
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_12,c_388])).

tff(c_1122,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1088,c_392])).

tff(c_1143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_1122])).

tff(c_1144,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_529,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k1_tops_1(A_156,B_157),B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1173,plain,(
    ! [A_208,A_209] :
      ( r1_tarski(k1_tops_1(A_208,A_209),A_209)
      | ~ l1_pre_topc(A_208)
      | ~ r1_tarski(A_209,u1_struct_0(A_208)) ) ),
    inference(resolution,[status(thm)],[c_8,c_529])).

tff(c_1182,plain,(
    ! [A_208,A_4] :
      ( r1_tarski(k1_tops_1(A_208,k1_xboole_0),A_4)
      | ~ l1_pre_topc(A_208)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_208)) ) ),
    inference(resolution,[status(thm)],[c_1173,c_426])).

tff(c_1203,plain,(
    ! [A_210,A_211] :
      ( r1_tarski(k1_tops_1(A_210,k1_xboole_0),A_211)
      | ~ l1_pre_topc(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1182])).

tff(c_1225,plain,(
    ! [A_212] :
      ( k1_tops_1(A_212,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_1203,c_392])).

tff(c_1229,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1225])).

tff(c_1459,plain,(
    ! [A_232,B_233,C_234] :
      ( r1_tarski(k1_tops_1(A_232,B_233),k1_tops_1(A_232,C_234))
      | ~ r1_tarski(B_233,C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1478,plain,(
    ! [B_233] :
      ( r1_tarski(k1_tops_1('#skF_2',B_233),k1_xboole_0)
      | ~ r1_tarski(B_233,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_1459])).

tff(c_1500,plain,(
    ! [B_233] :
      ( r1_tarski(k1_tops_1('#skF_2',B_233),k1_xboole_0)
      | ~ r1_tarski(B_233,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1478])).

tff(c_1590,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1500])).

tff(c_1593,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_1590])).

tff(c_1597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1593])).

tff(c_1599,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_26,plain,(
    ! [B_47,D_53,C_51,A_39] :
      ( k1_tops_1(B_47,D_53) = D_53
      | ~ v3_pre_topc(D_53,B_47)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(B_47)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(B_47)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1806,plain,(
    ! [C_243,A_244] :
      ( ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_1809,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1599,c_1806])).

tff(c_1823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1809])).

tff(c_1965,plain,(
    ! [B_250,D_251] :
      ( k1_tops_1(B_250,D_251) = D_251
      | ~ v3_pre_topc(D_251,B_250)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(u1_struct_0(B_250)))
      | ~ l1_pre_topc(B_250) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1975,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_1965])).

tff(c_1985,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_385,c_1144,c_1975])).

tff(c_1987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_1985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:01:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.90  
% 3.62/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.90  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.62/1.90  
% 3.62/1.90  %Foreground sorts:
% 3.62/1.90  
% 3.62/1.90  
% 3.62/1.90  %Background operators:
% 3.62/1.90  
% 3.62/1.90  
% 3.62/1.90  %Foreground operators:
% 3.62/1.90  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.62/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.90  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.62/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.90  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.62/1.90  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.90  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.90  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.62/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.90  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.62/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.90  
% 3.96/1.92  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.96/1.92  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.96/1.92  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.96/1.92  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.96/1.92  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.96/1.92  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.96/1.92  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.96/1.92  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.96/1.92  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.96/1.92  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.96/1.92  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.96/1.92  tff(c_38, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_58, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 3.96/1.92  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_187, plain, (![B_102, A_103]: (v2_tops_1(B_102, A_103) | k1_tops_1(A_103, B_102)!=k1_xboole_0 | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.96/1.92  tff(c_194, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_187])).
% 3.96/1.92  tff(c_198, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_194])).
% 3.96/1.92  tff(c_199, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_198])).
% 3.96/1.92  tff(c_117, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.96/1.92  tff(c_122, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_117])).
% 3.96/1.92  tff(c_126, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_122])).
% 3.96/1.92  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_284, plain, (![A_116, B_117]: (v3_pre_topc(k1_tops_1(A_116, B_117), A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.92  tff(c_289, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_284])).
% 3.96/1.92  tff(c_293, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_289])).
% 3.96/1.92  tff(c_73, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.92  tff(c_81, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_73])).
% 3.96/1.92  tff(c_82, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.92  tff(c_87, plain, (![A_74]: (r1_tarski(A_74, u1_struct_0('#skF_2')) | ~r1_tarski(A_74, '#skF_3'))), inference(resolution, [status(thm)], [c_81, c_82])).
% 3.96/1.92  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.92  tff(c_56, plain, (![C_64]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_64 | ~v3_pre_topc(C_64, '#skF_2') | ~r1_tarski(C_64, '#skF_3') | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_325, plain, (![C_121]: (k1_xboole_0=C_121 | ~v3_pre_topc(C_121, '#skF_2') | ~r1_tarski(C_121, '#skF_3') | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_56])).
% 3.96/1.92  tff(c_340, plain, (![A_123]: (k1_xboole_0=A_123 | ~v3_pre_topc(A_123, '#skF_2') | ~r1_tarski(A_123, '#skF_3') | ~r1_tarski(A_123, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_325])).
% 3.96/1.92  tff(c_367, plain, (![A_124]: (k1_xboole_0=A_124 | ~v3_pre_topc(A_124, '#skF_2') | ~r1_tarski(A_124, '#skF_3'))), inference(resolution, [status(thm)], [c_87, c_340])).
% 3.96/1.92  tff(c_370, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_293, c_367])).
% 3.96/1.92  tff(c_376, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_370])).
% 3.96/1.92  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_376])).
% 3.96/1.92  tff(c_379, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 3.96/1.92  tff(c_380, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.96/1.92  tff(c_40, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_385, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_40])).
% 3.96/1.92  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_387, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_44])).
% 3.96/1.92  tff(c_612, plain, (![A_165, B_166]: (k1_tops_1(A_165, B_166)=k1_xboole_0 | ~v2_tops_1(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.96/1.92  tff(c_619, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_387, c_612])).
% 3.96/1.92  tff(c_626, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_619])).
% 3.96/1.92  tff(c_637, plain, (~v2_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_626])).
% 3.96/1.92  tff(c_825, plain, (![B_186, A_187]: (v2_tops_1(B_186, A_187) | k1_tops_1(A_187, B_186)!=k1_xboole_0 | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.96/1.92  tff(c_832, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_387, c_825])).
% 3.96/1.92  tff(c_839, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_832])).
% 3.96/1.92  tff(c_840, plain, (k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_637, c_839])).
% 3.96/1.92  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.96/1.92  tff(c_383, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_42])).
% 3.96/1.92  tff(c_622, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_612])).
% 3.96/1.92  tff(c_629, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_380, c_622])).
% 3.96/1.92  tff(c_979, plain, (![A_197, B_198, C_199]: (r1_tarski(k1_tops_1(A_197, B_198), k1_tops_1(A_197, C_199)) | ~r1_tarski(B_198, C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.92  tff(c_1010, plain, (![B_198]: (r1_tarski(k1_tops_1('#skF_2', B_198), k1_xboole_0) | ~r1_tarski(B_198, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_629, c_979])).
% 3.96/1.92  tff(c_1030, plain, (![B_200]: (r1_tarski(k1_tops_1('#skF_2', B_200), k1_xboole_0) | ~r1_tarski(B_200, '#skF_3') | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1010])).
% 3.96/1.92  tff(c_1037, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_387, c_1030])).
% 3.96/1.92  tff(c_1044, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_1037])).
% 3.96/1.92  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.92  tff(c_414, plain, (![A_133, C_134, B_135]: (r1_tarski(A_133, C_134) | ~r1_tarski(B_135, C_134) | ~r1_tarski(A_133, B_135))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.92  tff(c_426, plain, (![A_133, A_4]: (r1_tarski(A_133, A_4) | ~r1_tarski(A_133, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_414])).
% 3.96/1.92  tff(c_1088, plain, (![A_201]: (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_201))), inference(resolution, [status(thm)], [c_1044, c_426])).
% 3.96/1.92  tff(c_12, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/1.92  tff(c_388, plain, (![B_126, A_127]: (~r1_tarski(B_126, A_127) | ~r2_hidden(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.96/1.92  tff(c_392, plain, (![A_9]: (~r1_tarski(A_9, '#skF_1'(A_9)) | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_12, c_388])).
% 3.96/1.92  tff(c_1122, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1088, c_392])).
% 3.96/1.92  tff(c_1143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_840, c_1122])).
% 3.96/1.92  tff(c_1144, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_626])).
% 3.96/1.92  tff(c_529, plain, (![A_156, B_157]: (r1_tarski(k1_tops_1(A_156, B_157), B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.96/1.92  tff(c_1173, plain, (![A_208, A_209]: (r1_tarski(k1_tops_1(A_208, A_209), A_209) | ~l1_pre_topc(A_208) | ~r1_tarski(A_209, u1_struct_0(A_208)))), inference(resolution, [status(thm)], [c_8, c_529])).
% 3.96/1.92  tff(c_1182, plain, (![A_208, A_4]: (r1_tarski(k1_tops_1(A_208, k1_xboole_0), A_4) | ~l1_pre_topc(A_208) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_208)))), inference(resolution, [status(thm)], [c_1173, c_426])).
% 3.96/1.92  tff(c_1203, plain, (![A_210, A_211]: (r1_tarski(k1_tops_1(A_210, k1_xboole_0), A_211) | ~l1_pre_topc(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1182])).
% 3.96/1.92  tff(c_1225, plain, (![A_212]: (k1_tops_1(A_212, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_1203, c_392])).
% 3.96/1.92  tff(c_1229, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1225])).
% 3.96/1.92  tff(c_1459, plain, (![A_232, B_233, C_234]: (r1_tarski(k1_tops_1(A_232, B_233), k1_tops_1(A_232, C_234)) | ~r1_tarski(B_233, C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(u1_struct_0(A_232))) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.92  tff(c_1478, plain, (![B_233]: (r1_tarski(k1_tops_1('#skF_2', B_233), k1_xboole_0) | ~r1_tarski(B_233, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_1459])).
% 3.96/1.92  tff(c_1500, plain, (![B_233]: (r1_tarski(k1_tops_1('#skF_2', B_233), k1_xboole_0) | ~r1_tarski(B_233, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1478])).
% 3.96/1.92  tff(c_1590, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1500])).
% 3.96/1.92  tff(c_1593, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1590])).
% 3.96/1.92  tff(c_1597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1593])).
% 3.96/1.92  tff(c_1599, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1500])).
% 3.96/1.92  tff(c_26, plain, (![B_47, D_53, C_51, A_39]: (k1_tops_1(B_47, D_53)=D_53 | ~v3_pre_topc(D_53, B_47) | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0(B_47))) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(B_47) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.96/1.92  tff(c_1806, plain, (![C_243, A_244]: (~m1_subset_1(C_243, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244))), inference(splitLeft, [status(thm)], [c_26])).
% 3.96/1.92  tff(c_1809, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1599, c_1806])).
% 3.96/1.92  tff(c_1823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1809])).
% 3.96/1.92  tff(c_1965, plain, (![B_250, D_251]: (k1_tops_1(B_250, D_251)=D_251 | ~v3_pre_topc(D_251, B_250) | ~m1_subset_1(D_251, k1_zfmisc_1(u1_struct_0(B_250))) | ~l1_pre_topc(B_250))), inference(splitRight, [status(thm)], [c_26])).
% 3.96/1.92  tff(c_1975, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_387, c_1965])).
% 3.96/1.92  tff(c_1985, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_385, c_1144, c_1975])).
% 3.96/1.92  tff(c_1987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_1985])).
% 3.96/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.92  
% 3.96/1.92  Inference rules
% 3.96/1.92  ----------------------
% 3.96/1.92  #Ref     : 0
% 3.96/1.92  #Sup     : 399
% 3.96/1.92  #Fact    : 0
% 3.96/1.92  #Define  : 0
% 3.96/1.92  #Split   : 14
% 3.96/1.92  #Chain   : 0
% 3.96/1.92  #Close   : 0
% 3.96/1.92  
% 3.96/1.92  Ordering : KBO
% 3.96/1.92  
% 3.96/1.92  Simplification rules
% 3.96/1.92  ----------------------
% 3.96/1.92  #Subsume      : 112
% 3.96/1.92  #Demod        : 358
% 3.96/1.92  #Tautology    : 140
% 3.96/1.92  #SimpNegUnit  : 10
% 3.96/1.92  #BackRed      : 5
% 3.96/1.92  
% 3.96/1.92  #Partial instantiations: 0
% 3.96/1.92  #Strategies tried      : 1
% 3.96/1.92  
% 3.96/1.92  Timing (in seconds)
% 3.96/1.92  ----------------------
% 3.96/1.93  Preprocessing        : 0.47
% 3.96/1.93  Parsing              : 0.26
% 3.96/1.93  CNF conversion       : 0.03
% 3.96/1.93  Main loop            : 0.53
% 3.96/1.93  Inferencing          : 0.19
% 3.96/1.93  Reduction            : 0.17
% 3.96/1.93  Demodulation         : 0.12
% 3.96/1.93  BG Simplification    : 0.02
% 3.96/1.93  Subsumption          : 0.11
% 3.96/1.93  Abstraction          : 0.02
% 3.96/1.93  MUC search           : 0.00
% 3.96/1.93  Cooper               : 0.00
% 3.96/1.93  Total                : 1.05
% 3.96/1.93  Index Insertion      : 0.00
% 3.96/1.93  Index Deletion       : 0.00
% 3.96/1.93  Index Matching       : 0.00
% 3.96/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
