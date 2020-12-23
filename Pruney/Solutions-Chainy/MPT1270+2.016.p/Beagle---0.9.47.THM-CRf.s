%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 122 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 237 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_596,plain,(
    ! [B_170,A_171] :
      ( r1_tarski(B_170,k2_pre_topc(A_171,B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_598,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_596])).

tff(c_604,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_598])).

tff(c_4,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_719,plain,(
    ! [A_193,B_194] :
      ( m1_subset_1(k2_pre_topc(A_193,B_194),k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( k7_subset_1(A_9,B_10,C_11) = k4_xboole_0(B_10,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1253,plain,(
    ! [A_281,B_282,C_283] :
      ( k7_subset_1(u1_struct_0(A_281),k2_pre_topc(A_281,B_282),C_283) = k4_xboole_0(k2_pre_topc(A_281,B_282),C_283)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_719,c_12])).

tff(c_1257,plain,(
    ! [C_283] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_283) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_283)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_1253])).

tff(c_1266,plain,(
    ! [C_284] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_284) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1257])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3'))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_220,plain,(
    ! [B_95,A_96] :
      ( v2_tops_1(B_95,A_96)
      | k1_tops_1(A_96,B_95) != k1_xboole_0
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_223,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_230,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_223])).

tff(c_231,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_230])).

tff(c_124,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tops_1(A_79,B_80),B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_126,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_132,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_126])).

tff(c_44,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_67,plain,(
    r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_44])).

tff(c_83,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,k2_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_67,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_83])).

tff(c_215,plain,(
    ! [A_93,B_94] :
      ( r1_xboole_0(k1_tops_1(A_93,B_94),k2_tops_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | ~ r1_tarski(B_6,A_5)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_536,plain,(
    ! [A_151,B_152] :
      ( ~ r1_tarski(k1_tops_1(A_151,B_152),k2_tops_1(A_151,B_152))
      | v1_xboole_0(k1_tops_1(A_151,B_152))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_215,c_6])).

tff(c_540,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_536])).

tff(c_543,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_36,c_34,c_540])).

tff(c_18,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_69,plain,(
    ! [C_61,B_62,A_63] :
      ( ~ v1_xboole_0(C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_64,A_65] :
      ( ~ v1_xboole_0(A_64)
      | ~ r2_hidden(A_65,A_64) ) ),
    inference(resolution,[status(thm)],[c_45,c_69])).

tff(c_80,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_546,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_543,c_80])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_546])).

tff(c_552,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_678,plain,(
    ! [A_188,B_189] :
      ( k1_tops_1(A_188,B_189) = k1_xboole_0
      | ~ v2_tops_1(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_681,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_678])).

tff(c_688,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_552,c_681])).

tff(c_804,plain,(
    ! [A_210,B_211] :
      ( k7_subset_1(u1_struct_0(A_210),k2_pre_topc(A_210,B_211),k1_tops_1(A_210,B_211)) = k2_tops_1(A_210,B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_813,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k1_xboole_0) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_804])).

tff(c_817,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k1_xboole_0) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_813])).

tff(c_1272,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_xboole_0) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_817])).

tff(c_1288,plain,(
    k2_tops_1('#skF_2','#skF_3') = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1272])).

tff(c_551,plain,(
    ~ r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1298,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_551])).

tff(c_1301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_1298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  
% 3.88/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  %$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.88/1.67  
% 3.88/1.67  %Foreground sorts:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Background operators:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Foreground operators:
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.67  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.88/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.88/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.67  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.88/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.88/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.88/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.88/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.88/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/1.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.88/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.67  
% 4.10/1.69  tff(f_130, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.10/1.69  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.10/1.69  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.10/1.69  tff(f_83, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.10/1.69  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.10/1.69  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.10/1.69  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.10/1.69  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.10/1.69  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 4.10/1.69  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.10/1.69  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.10/1.69  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.10/1.69  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.10/1.69  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.10/1.69  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.10/1.69  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.10/1.69  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.10/1.69  tff(c_596, plain, (![B_170, A_171]: (r1_tarski(B_170, k2_pre_topc(A_171, B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.10/1.69  tff(c_598, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_596])).
% 4.10/1.69  tff(c_604, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_598])).
% 4.10/1.69  tff(c_4, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.10/1.69  tff(c_719, plain, (![A_193, B_194]: (m1_subset_1(k2_pre_topc(A_193, B_194), k1_zfmisc_1(u1_struct_0(A_193))) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.10/1.69  tff(c_12, plain, (![A_9, B_10, C_11]: (k7_subset_1(A_9, B_10, C_11)=k4_xboole_0(B_10, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.10/1.69  tff(c_1253, plain, (![A_281, B_282, C_283]: (k7_subset_1(u1_struct_0(A_281), k2_pre_topc(A_281, B_282), C_283)=k4_xboole_0(k2_pre_topc(A_281, B_282), C_283) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_719, c_12])).
% 4.10/1.69  tff(c_1257, plain, (![C_283]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_283)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_283) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_1253])).
% 4.10/1.69  tff(c_1266, plain, (![C_284]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_284)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_284))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1257])).
% 4.10/1.69  tff(c_38, plain, (~r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3')) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.10/1.69  tff(c_66, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 4.10/1.69  tff(c_220, plain, (![B_95, A_96]: (v2_tops_1(B_95, A_96) | k1_tops_1(A_96, B_95)!=k1_xboole_0 | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.10/1.69  tff(c_223, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_220])).
% 4.10/1.69  tff(c_230, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_223])).
% 4.10/1.69  tff(c_231, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_230])).
% 4.10/1.69  tff(c_124, plain, (![A_79, B_80]: (r1_tarski(k1_tops_1(A_79, B_80), B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.10/1.69  tff(c_126, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_124])).
% 4.10/1.69  tff(c_132, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_126])).
% 4.10/1.69  tff(c_44, plain, (v2_tops_1('#skF_3', '#skF_2') | r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.10/1.69  tff(c_67, plain, (r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_44])).
% 4.10/1.69  tff(c_83, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.69  tff(c_86, plain, (![A_67]: (r1_tarski(A_67, k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(A_67, '#skF_3'))), inference(resolution, [status(thm)], [c_67, c_83])).
% 4.10/1.69  tff(c_215, plain, (![A_93, B_94]: (r1_xboole_0(k1_tops_1(A_93, B_94), k2_tops_1(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.10/1.69  tff(c_6, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | ~r1_tarski(B_6, A_5) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.10/1.69  tff(c_536, plain, (![A_151, B_152]: (~r1_tarski(k1_tops_1(A_151, B_152), k2_tops_1(A_151, B_152)) | v1_xboole_0(k1_tops_1(A_151, B_152)) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_215, c_6])).
% 4.10/1.69  tff(c_540, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_86, c_536])).
% 4.10/1.69  tff(c_543, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_36, c_34, c_540])).
% 4.10/1.69  tff(c_18, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.69  tff(c_8, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.69  tff(c_10, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.69  tff(c_45, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 4.10/1.69  tff(c_69, plain, (![C_61, B_62, A_63]: (~v1_xboole_0(C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.10/1.69  tff(c_76, plain, (![A_64, A_65]: (~v1_xboole_0(A_64) | ~r2_hidden(A_65, A_64))), inference(resolution, [status(thm)], [c_45, c_69])).
% 4.10/1.69  tff(c_80, plain, (![A_15]: (~v1_xboole_0(A_15) | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_18, c_76])).
% 4.10/1.69  tff(c_546, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_543, c_80])).
% 4.10/1.69  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_546])).
% 4.10/1.69  tff(c_552, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 4.10/1.69  tff(c_678, plain, (![A_188, B_189]: (k1_tops_1(A_188, B_189)=k1_xboole_0 | ~v2_tops_1(B_189, A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.10/1.69  tff(c_681, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_678])).
% 4.10/1.69  tff(c_688, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_552, c_681])).
% 4.10/1.69  tff(c_804, plain, (![A_210, B_211]: (k7_subset_1(u1_struct_0(A_210), k2_pre_topc(A_210, B_211), k1_tops_1(A_210, B_211))=k2_tops_1(A_210, B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.10/1.69  tff(c_813, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k1_xboole_0)=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_688, c_804])).
% 4.10/1.69  tff(c_817, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k1_xboole_0)=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_813])).
% 4.10/1.69  tff(c_1272, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_xboole_0)=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_817])).
% 4.10/1.69  tff(c_1288, plain, (k2_tops_1('#skF_2', '#skF_3')=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1272])).
% 4.10/1.69  tff(c_551, plain, (~r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 4.10/1.69  tff(c_1298, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_551])).
% 4.10/1.69  tff(c_1301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_604, c_1298])).
% 4.10/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.69  
% 4.10/1.69  Inference rules
% 4.10/1.69  ----------------------
% 4.10/1.69  #Ref     : 0
% 4.10/1.69  #Sup     : 308
% 4.10/1.69  #Fact    : 0
% 4.10/1.69  #Define  : 0
% 4.10/1.69  #Split   : 11
% 4.10/1.69  #Chain   : 0
% 4.10/1.69  #Close   : 0
% 4.10/1.69  
% 4.10/1.69  Ordering : KBO
% 4.10/1.69  
% 4.10/1.69  Simplification rules
% 4.10/1.69  ----------------------
% 4.10/1.69  #Subsume      : 48
% 4.10/1.69  #Demod        : 63
% 4.10/1.69  #Tautology    : 41
% 4.10/1.69  #SimpNegUnit  : 5
% 4.10/1.69  #BackRed      : 6
% 4.10/1.69  
% 4.10/1.69  #Partial instantiations: 0
% 4.10/1.69  #Strategies tried      : 1
% 4.10/1.69  
% 4.10/1.69  Timing (in seconds)
% 4.10/1.69  ----------------------
% 4.10/1.69  Preprocessing        : 0.34
% 4.10/1.69  Parsing              : 0.18
% 4.10/1.69  CNF conversion       : 0.02
% 4.10/1.69  Main loop            : 0.58
% 4.10/1.69  Inferencing          : 0.22
% 4.10/1.69  Reduction            : 0.15
% 4.10/1.69  Demodulation         : 0.10
% 4.10/1.69  BG Simplification    : 0.03
% 4.10/1.69  Subsumption          : 0.14
% 4.10/1.69  Abstraction          : 0.03
% 4.10/1.69  MUC search           : 0.00
% 4.10/1.69  Cooper               : 0.00
% 4.10/1.69  Total                : 0.96
% 4.10/1.69  Index Insertion      : 0.00
% 4.10/1.69  Index Deletion       : 0.00
% 4.10/1.69  Index Matching       : 0.00
% 4.10/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
