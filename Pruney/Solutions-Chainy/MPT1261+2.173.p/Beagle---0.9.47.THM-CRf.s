%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 180 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 357 expanded)
%              Number of equality atoms :   53 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5969,plain,(
    ! [A_242,B_243,C_244] :
      ( k7_subset_1(A_242,B_243,C_244) = k4_xboole_0(B_243,C_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5972,plain,(
    ! [C_244] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_244) = k4_xboole_0('#skF_2',C_244) ),
    inference(resolution,[status(thm)],[c_30,c_5969])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1056,plain,(
    ! [A_107,B_108] :
      ( k4_subset_1(u1_struct_0(A_107),B_108,k2_tops_1(A_107,B_108)) = k2_pre_topc(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1060,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1056])).

tff(c_1064,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1060])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_subset_1(A_61,B_62,C_63) = k4_xboole_0(B_62,C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [C_63] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_63) = k4_xboole_0('#skF_2',C_63) ),
    inference(resolution,[status(thm)],[c_30,c_115])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_194,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_42])).

tff(c_195,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_194])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_48,A_49,B_50] :
      ( r1_tarski(A_48,A_49)
      | ~ r1_tarski(A_48,k4_xboole_0(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_82,plain,(
    ! [A_49,B_50,B_9] : r1_tarski(k4_xboole_0(k4_xboole_0(A_49,B_50),B_9),A_49) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_346,plain,(
    ! [B_74] : r1_tarski(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_74),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_82])).

tff(c_101,plain,(
    ! [C_58,B_59,A_60] :
      ( r1_tarski(k4_xboole_0(C_58,B_59),k4_xboole_0(C_58,A_60))
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    ! [C_58,B_59] :
      ( k4_xboole_0(C_58,B_59) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_58,B_59),B_59) ) ),
    inference(resolution,[status(thm)],[c_101,c_10])).

tff(c_356,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_346,c_114])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_525,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_12])).

tff(c_542,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_525])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_613,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5656,plain,(
    ! [A_216,B_217,B_218] :
      ( k4_subset_1(u1_struct_0(A_216),B_217,k2_tops_1(A_216,B_218)) = k2_xboole_0(B_217,k2_tops_1(A_216,B_218))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(resolution,[status(thm)],[c_20,c_613])).

tff(c_5660,plain,(
    ! [B_218] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_218)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_218))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_5656])).

tff(c_5665,plain,(
    ! [B_219] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_219)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5660])).

tff(c_5672,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_5665])).

tff(c_5677,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_542,c_5672])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_268,plain,(
    ! [A_70,B_71] :
      ( v4_pre_topc(k2_pre_topc(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_270,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_268])).

tff(c_273,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_270])).

tff(c_5679,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_273])).

tff(c_5681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5679])).

tff(c_5682,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_6031,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5972,c_5682])).

tff(c_7000,plain,(
    ! [A_286,B_287] :
      ( k4_subset_1(u1_struct_0(A_286),B_287,k2_tops_1(A_286,B_287)) = k2_pre_topc(A_286,B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7004,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_7000])).

tff(c_7008,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_7004])).

tff(c_5683,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_6108,plain,(
    ! [A_258,B_259] :
      ( r1_tarski(k2_tops_1(A_258,B_259),B_259)
      | ~ v4_pre_topc(B_259,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6112,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6108])).

tff(c_6116,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5683,c_6112])).

tff(c_5708,plain,(
    ! [C_230,B_231,A_232] :
      ( r1_tarski(k4_xboole_0(C_230,B_231),k4_xboole_0(C_230,A_232))
      | ~ r1_tarski(A_232,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5722,plain,(
    ! [C_233,B_234] :
      ( k4_xboole_0(C_233,B_234) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_233,B_234),B_234) ) ),
    inference(resolution,[status(thm)],[c_5708,c_10])).

tff(c_5743,plain,(
    ! [A_235] : k4_xboole_0(A_235,A_235) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_5722])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5] :
      ( r1_tarski(k4_xboole_0(C_7,B_6),k4_xboole_0(C_7,A_5))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6051,plain,(
    ! [A_254,B_255] :
      ( r1_tarski(k4_xboole_0(A_254,B_255),k1_xboole_0)
      | ~ r1_tarski(A_254,B_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5743,c_6])).

tff(c_5778,plain,(
    ! [A_235] :
      ( k1_xboole_0 = A_235
      | ~ r1_tarski(A_235,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5743,c_10])).

tff(c_6073,plain,(
    ! [A_254,B_255] :
      ( k4_xboole_0(A_254,B_255) = k1_xboole_0
      | ~ r1_tarski(A_254,B_255) ) ),
    inference(resolution,[status(thm)],[c_6051,c_5778])).

tff(c_6122,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6116,c_6073])).

tff(c_6154,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6122,c_12])).

tff(c_6172,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6154])).

tff(c_6386,plain,(
    ! [A_268,B_269,C_270] :
      ( k4_subset_1(A_268,B_269,C_270) = k2_xboole_0(B_269,C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(A_268))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(A_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12668,plain,(
    ! [A_415,B_416,B_417] :
      ( k4_subset_1(u1_struct_0(A_415),B_416,k2_tops_1(A_415,B_417)) = k2_xboole_0(B_416,k2_tops_1(A_415,B_417))
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_20,c_6386])).

tff(c_12672,plain,(
    ! [B_417] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_417)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_417))
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_12668])).

tff(c_13614,plain,(
    ! [B_426] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_426)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_426))
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12672])).

tff(c_13621,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_13614])).

tff(c_13626,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7008,c_6172,c_13621])).

tff(c_24,plain,(
    ! [A_26,B_28] :
      ( k7_subset_1(u1_struct_0(A_26),k2_pre_topc(A_26,B_28),k1_tops_1(A_26,B_28)) = k2_tops_1(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13633,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13626,c_24])).

tff(c_13637,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_5972,c_13633])).

tff(c_13639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6031,c_13637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.76  
% 7.57/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.76  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.57/2.76  
% 7.57/2.76  %Foreground sorts:
% 7.57/2.76  
% 7.57/2.76  
% 7.57/2.76  %Background operators:
% 7.57/2.76  
% 7.57/2.76  
% 7.57/2.76  %Foreground operators:
% 7.57/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.57/2.76  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.57/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/2.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.57/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.57/2.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.57/2.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.57/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.76  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.57/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.57/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.57/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.57/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.57/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.57/2.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.57/2.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.57/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.76  
% 7.80/2.78  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.80/2.78  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.80/2.78  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.80/2.78  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.80/2.78  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.80/2.78  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.80/2.78  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 7.80/2.78  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.80/2.78  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.80/2.78  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.80/2.78  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.80/2.78  tff(f_71, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 7.80/2.78  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 7.80/2.78  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.80/2.78  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.80/2.78  tff(c_5969, plain, (![A_242, B_243, C_244]: (k7_subset_1(A_242, B_243, C_244)=k4_xboole_0(B_243, C_244) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.80/2.78  tff(c_5972, plain, (![C_244]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_244)=k4_xboole_0('#skF_2', C_244))), inference(resolution, [status(thm)], [c_30, c_5969])).
% 7.80/2.78  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.80/2.78  tff(c_76, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 7.80/2.78  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.80/2.78  tff(c_1056, plain, (![A_107, B_108]: (k4_subset_1(u1_struct_0(A_107), B_108, k2_tops_1(A_107, B_108))=k2_pre_topc(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.80/2.78  tff(c_1060, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1056])).
% 7.80/2.78  tff(c_1064, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1060])).
% 7.80/2.78  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/2.78  tff(c_115, plain, (![A_61, B_62, C_63]: (k7_subset_1(A_61, B_62, C_63)=k4_xboole_0(B_62, C_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.80/2.78  tff(c_118, plain, (![C_63]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_63)=k4_xboole_0('#skF_2', C_63))), inference(resolution, [status(thm)], [c_30, c_115])).
% 7.80/2.78  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.80/2.78  tff(c_194, plain, (v4_pre_topc('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_42])).
% 7.80/2.78  tff(c_195, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_194])).
% 7.80/2.78  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/2.78  tff(c_72, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.80/2.78  tff(c_77, plain, (![A_48, A_49, B_50]: (r1_tarski(A_48, A_49) | ~r1_tarski(A_48, k4_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_8, c_72])).
% 7.80/2.78  tff(c_82, plain, (![A_49, B_50, B_9]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_49, B_50), B_9), A_49))), inference(resolution, [status(thm)], [c_8, c_77])).
% 7.80/2.78  tff(c_346, plain, (![B_74]: (r1_tarski(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_74), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_82])).
% 7.80/2.78  tff(c_101, plain, (![C_58, B_59, A_60]: (r1_tarski(k4_xboole_0(C_58, B_59), k4_xboole_0(C_58, A_60)) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/2.78  tff(c_10, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k4_xboole_0(B_11, A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.80/2.78  tff(c_114, plain, (![C_58, B_59]: (k4_xboole_0(C_58, B_59)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_58, B_59), B_59))), inference(resolution, [status(thm)], [c_101, c_10])).
% 7.80/2.78  tff(c_356, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_346, c_114])).
% 7.80/2.78  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.78  tff(c_525, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_356, c_12])).
% 7.80/2.78  tff(c_542, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_525])).
% 7.80/2.78  tff(c_20, plain, (![A_22, B_23]: (m1_subset_1(k2_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.80/2.78  tff(c_613, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/2.78  tff(c_5656, plain, (![A_216, B_217, B_218]: (k4_subset_1(u1_struct_0(A_216), B_217, k2_tops_1(A_216, B_218))=k2_xboole_0(B_217, k2_tops_1(A_216, B_218)) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(resolution, [status(thm)], [c_20, c_613])).
% 7.80/2.78  tff(c_5660, plain, (![B_218]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_218))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_218)) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_5656])).
% 7.80/2.78  tff(c_5665, plain, (![B_219]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_219))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5660])).
% 7.80/2.78  tff(c_5672, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_5665])).
% 7.80/2.78  tff(c_5677, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_542, c_5672])).
% 7.80/2.78  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.80/2.78  tff(c_268, plain, (![A_70, B_71]: (v4_pre_topc(k2_pre_topc(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.80/2.78  tff(c_270, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_268])).
% 7.80/2.78  tff(c_273, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_270])).
% 7.80/2.78  tff(c_5679, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_273])).
% 7.80/2.78  tff(c_5681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5679])).
% 7.80/2.78  tff(c_5682, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 7.80/2.78  tff(c_6031, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5972, c_5682])).
% 7.80/2.78  tff(c_7000, plain, (![A_286, B_287]: (k4_subset_1(u1_struct_0(A_286), B_287, k2_tops_1(A_286, B_287))=k2_pre_topc(A_286, B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.80/2.78  tff(c_7004, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_7000])).
% 7.80/2.78  tff(c_7008, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_7004])).
% 7.80/2.78  tff(c_5683, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 7.80/2.78  tff(c_6108, plain, (![A_258, B_259]: (r1_tarski(k2_tops_1(A_258, B_259), B_259) | ~v4_pre_topc(B_259, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.80/2.78  tff(c_6112, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6108])).
% 7.80/2.78  tff(c_6116, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5683, c_6112])).
% 7.80/2.78  tff(c_5708, plain, (![C_230, B_231, A_232]: (r1_tarski(k4_xboole_0(C_230, B_231), k4_xboole_0(C_230, A_232)) | ~r1_tarski(A_232, B_231))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/2.78  tff(c_5722, plain, (![C_233, B_234]: (k4_xboole_0(C_233, B_234)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_233, B_234), B_234))), inference(resolution, [status(thm)], [c_5708, c_10])).
% 7.80/2.78  tff(c_5743, plain, (![A_235]: (k4_xboole_0(A_235, A_235)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_5722])).
% 7.80/2.78  tff(c_6, plain, (![C_7, B_6, A_5]: (r1_tarski(k4_xboole_0(C_7, B_6), k4_xboole_0(C_7, A_5)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/2.78  tff(c_6051, plain, (![A_254, B_255]: (r1_tarski(k4_xboole_0(A_254, B_255), k1_xboole_0) | ~r1_tarski(A_254, B_255))), inference(superposition, [status(thm), theory('equality')], [c_5743, c_6])).
% 7.80/2.78  tff(c_5778, plain, (![A_235]: (k1_xboole_0=A_235 | ~r1_tarski(A_235, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5743, c_10])).
% 7.80/2.78  tff(c_6073, plain, (![A_254, B_255]: (k4_xboole_0(A_254, B_255)=k1_xboole_0 | ~r1_tarski(A_254, B_255))), inference(resolution, [status(thm)], [c_6051, c_5778])).
% 7.80/2.78  tff(c_6122, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6116, c_6073])).
% 7.80/2.78  tff(c_6154, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6122, c_12])).
% 7.80/2.78  tff(c_6172, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6154])).
% 7.80/2.78  tff(c_6386, plain, (![A_268, B_269, C_270]: (k4_subset_1(A_268, B_269, C_270)=k2_xboole_0(B_269, C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(A_268)) | ~m1_subset_1(B_269, k1_zfmisc_1(A_268)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/2.78  tff(c_12668, plain, (![A_415, B_416, B_417]: (k4_subset_1(u1_struct_0(A_415), B_416, k2_tops_1(A_415, B_417))=k2_xboole_0(B_416, k2_tops_1(A_415, B_417)) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_415))) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_415))) | ~l1_pre_topc(A_415))), inference(resolution, [status(thm)], [c_20, c_6386])).
% 7.80/2.78  tff(c_12672, plain, (![B_417]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_417))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_417)) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_12668])).
% 7.80/2.78  tff(c_13614, plain, (![B_426]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_426))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_426)) | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12672])).
% 7.80/2.78  tff(c_13621, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_13614])).
% 7.80/2.78  tff(c_13626, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7008, c_6172, c_13621])).
% 7.80/2.78  tff(c_24, plain, (![A_26, B_28]: (k7_subset_1(u1_struct_0(A_26), k2_pre_topc(A_26, B_28), k1_tops_1(A_26, B_28))=k2_tops_1(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.80/2.78  tff(c_13633, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13626, c_24])).
% 7.80/2.78  tff(c_13637, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_5972, c_13633])).
% 7.80/2.78  tff(c_13639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6031, c_13637])).
% 7.80/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.78  
% 7.80/2.78  Inference rules
% 7.80/2.78  ----------------------
% 7.80/2.78  #Ref     : 0
% 7.80/2.78  #Sup     : 3264
% 7.80/2.78  #Fact    : 0
% 7.80/2.78  #Define  : 0
% 7.80/2.78  #Split   : 5
% 7.80/2.78  #Chain   : 0
% 7.80/2.78  #Close   : 0
% 7.80/2.78  
% 7.80/2.78  Ordering : KBO
% 7.80/2.78  
% 7.80/2.78  Simplification rules
% 7.80/2.78  ----------------------
% 7.80/2.78  #Subsume      : 537
% 7.80/2.78  #Demod        : 3076
% 7.80/2.78  #Tautology    : 2274
% 7.80/2.78  #SimpNegUnit  : 3
% 7.80/2.78  #BackRed      : 5
% 7.80/2.78  
% 7.80/2.78  #Partial instantiations: 0
% 7.80/2.78  #Strategies tried      : 1
% 7.80/2.78  
% 7.80/2.78  Timing (in seconds)
% 7.80/2.78  ----------------------
% 7.80/2.78  Preprocessing        : 0.36
% 7.80/2.78  Parsing              : 0.19
% 7.80/2.78  CNF conversion       : 0.02
% 7.80/2.78  Main loop            : 1.59
% 7.80/2.78  Inferencing          : 0.48
% 7.80/2.78  Reduction            : 0.63
% 7.80/2.78  Demodulation         : 0.49
% 7.80/2.78  BG Simplification    : 0.06
% 7.80/2.78  Subsumption          : 0.33
% 7.80/2.78  Abstraction          : 0.07
% 7.80/2.78  MUC search           : 0.00
% 7.80/2.78  Cooper               : 0.00
% 7.80/2.78  Total                : 1.99
% 7.80/2.78  Index Insertion      : 0.00
% 7.80/2.78  Index Deletion       : 0.00
% 7.80/2.78  Index Matching       : 0.00
% 7.80/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
