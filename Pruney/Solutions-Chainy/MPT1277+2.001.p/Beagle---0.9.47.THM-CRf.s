%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:07 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 448 expanded)
%              Number of leaves         :   33 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 946 expanded)
%              Number of equality atoms :   26 ( 264 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

tff(c_26,plain,(
    ~ v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_213,plain,(
    ! [A_57,B_58] :
      ( k4_subset_1(u1_struct_0(A_57),B_58,k3_subset_1(u1_struct_0(A_57),B_58)) = k2_struct_0(A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_subset_1(A_10,B_11,k3_subset_1(A_10,B_11)) = k2_subset_1(A_10)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( k4_subset_1(A_34,B_35,k3_subset_1(A_34,B_35)) = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_83,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_75])).

tff(c_223,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_83])).

tff(c_244,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_223])).

tff(c_252,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_255])).

tff(c_260,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_268,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_30])).

tff(c_28,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_49,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_267,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_60])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_98,plain,(
    ! [A_37,B_38,C_39] :
      ( k7_subset_1(A_37,B_38,C_39) = k4_xboole_0(B_38,C_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_4,C_39] : k7_subset_1(A_4,A_4,C_39) = k4_xboole_0(A_4,C_39) ),
    inference(resolution,[status(thm)],[c_35,c_98])).

tff(c_367,plain,(
    ! [A_64,B_65] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_64),k2_struct_0(A_64),B_65),A_64)
      | ~ v4_pre_topc(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_370,plain,(
    ! [B_65] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_65),'#skF_1')
      | ~ v4_pre_topc(B_65,'#skF_1')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_367])).

tff(c_465,plain,(
    ! [B_73] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_73),'#skF_1')
      | ~ v4_pre_topc(B_73,'#skF_1')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_260,c_107,c_370])).

tff(c_474,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_465])).

tff(c_485,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_28,c_474])).

tff(c_186,plain,(
    ! [A_54,B_55] :
      ( k2_tops_1(A_54,k3_subset_1(u1_struct_0(A_54),B_55)) = k2_tops_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_198,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_191])).

tff(c_262,plain,(
    k2_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_198])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,k3_subset_1(A_43,B_44)) = k3_subset_1(A_43,k3_subset_1(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_8,c_49])).

tff(c_134,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_264,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_260,c_260,c_134])).

tff(c_471,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_465])).

tff(c_525,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_528,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_525])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_528])).

tff(c_534,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_315,plain,(
    ! [A_59,B_60] :
      ( v3_tops_1(k2_tops_1(A_59,B_60),A_59)
      | ~ v3_pre_topc(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_317,plain,(
    ! [B_60] :
      ( v3_tops_1(k2_tops_1('#skF_1',B_60),'#skF_1')
      | ~ v3_pre_topc(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_315])).

tff(c_325,plain,(
    ! [B_60] :
      ( v3_tops_1(k2_tops_1('#skF_1',B_60),'#skF_1')
      | ~ v3_pre_topc(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_317])).

tff(c_540,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_534,c_325])).

tff(c_556,plain,(
    v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_262,c_540])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.49  
% 2.85/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.49  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.85/1.49  
% 2.85/1.49  %Foreground sorts:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Background operators:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Foreground operators:
% 2.85/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.85/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.49  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.85/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.85/1.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.85/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.85/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.85/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.85/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.85/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.49  
% 2.85/1.50  tff(f_95, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tops_1)).
% 2.85/1.50  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.85/1.50  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.85/1.50  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.85/1.50  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.85/1.50  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.85/1.50  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.85/1.50  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.85/1.50  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.85/1.50  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 2.85/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.85/1.50  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tops_1)).
% 2.85/1.50  tff(c_26, plain, (~v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.50  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.50  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.50  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.50  tff(c_213, plain, (![A_57, B_58]: (k4_subset_1(u1_struct_0(A_57), B_58, k3_subset_1(u1_struct_0(A_57), B_58))=k2_struct_0(A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.50  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.50  tff(c_12, plain, (![A_10, B_11]: (k4_subset_1(A_10, B_11, k3_subset_1(A_10, B_11))=k2_subset_1(A_10) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.85/1.50  tff(c_75, plain, (![A_34, B_35]: (k4_subset_1(A_34, B_35, k3_subset_1(A_34, B_35))=A_34 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.85/1.50  tff(c_83, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_75])).
% 2.85/1.50  tff(c_223, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_213, c_83])).
% 2.85/1.50  tff(c_244, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_223])).
% 2.85/1.50  tff(c_252, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_244])).
% 2.85/1.50  tff(c_255, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_252])).
% 2.85/1.50  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_255])).
% 2.85/1.50  tff(c_260, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_244])).
% 2.85/1.50  tff(c_268, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_30])).
% 2.85/1.50  tff(c_28, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.50  tff(c_49, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.50  tff(c_60, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.85/1.50  tff(c_267, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_60])).
% 2.85/1.50  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.50  tff(c_35, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 2.85/1.50  tff(c_98, plain, (![A_37, B_38, C_39]: (k7_subset_1(A_37, B_38, C_39)=k4_xboole_0(B_38, C_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.50  tff(c_107, plain, (![A_4, C_39]: (k7_subset_1(A_4, A_4, C_39)=k4_xboole_0(A_4, C_39))), inference(resolution, [status(thm)], [c_35, c_98])).
% 2.85/1.50  tff(c_367, plain, (![A_64, B_65]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_64), k2_struct_0(A_64), B_65), A_64) | ~v4_pre_topc(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.50  tff(c_370, plain, (![B_65]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_65), '#skF_1') | ~v4_pre_topc(B_65, '#skF_1') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_367])).
% 2.85/1.50  tff(c_465, plain, (![B_73]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_73), '#skF_1') | ~v4_pre_topc(B_73, '#skF_1') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_260, c_107, c_370])).
% 2.85/1.50  tff(c_474, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_267, c_465])).
% 2.85/1.50  tff(c_485, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_28, c_474])).
% 2.85/1.50  tff(c_186, plain, (![A_54, B_55]: (k2_tops_1(A_54, k3_subset_1(u1_struct_0(A_54), B_55))=k2_tops_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.85/1.50  tff(c_191, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_186])).
% 2.85/1.50  tff(c_198, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_191])).
% 2.85/1.50  tff(c_262, plain, (k2_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_198])).
% 2.85/1.50  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.50  tff(c_126, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_subset_1(A_43, B_44))=k3_subset_1(A_43, k3_subset_1(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_8, c_49])).
% 2.85/1.50  tff(c_134, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_126])).
% 2.85/1.50  tff(c_264, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_260, c_260, c_134])).
% 2.85/1.50  tff(c_471, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_465])).
% 2.85/1.50  tff(c_525, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_471])).
% 2.85/1.50  tff(c_528, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_525])).
% 2.85/1.50  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_528])).
% 2.85/1.50  tff(c_534, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_471])).
% 2.85/1.50  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.50  tff(c_315, plain, (![A_59, B_60]: (v3_tops_1(k2_tops_1(A_59, B_60), A_59) | ~v3_pre_topc(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.85/1.50  tff(c_317, plain, (![B_60]: (v3_tops_1(k2_tops_1('#skF_1', B_60), '#skF_1') | ~v3_pre_topc(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_315])).
% 2.85/1.50  tff(c_325, plain, (![B_60]: (v3_tops_1(k2_tops_1('#skF_1', B_60), '#skF_1') | ~v3_pre_topc(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_317])).
% 2.85/1.50  tff(c_540, plain, (v3_tops_1(k2_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_534, c_325])).
% 2.85/1.50  tff(c_556, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_262, c_540])).
% 2.85/1.50  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_556])).
% 2.85/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.50  
% 2.85/1.50  Inference rules
% 2.85/1.50  ----------------------
% 2.85/1.50  #Ref     : 0
% 2.85/1.50  #Sup     : 122
% 2.85/1.50  #Fact    : 0
% 2.85/1.50  #Define  : 0
% 2.85/1.50  #Split   : 4
% 2.85/1.50  #Chain   : 0
% 2.85/1.50  #Close   : 0
% 2.85/1.51  
% 2.85/1.51  Ordering : KBO
% 2.85/1.51  
% 2.85/1.51  Simplification rules
% 2.85/1.51  ----------------------
% 2.85/1.51  #Subsume      : 5
% 2.85/1.51  #Demod        : 78
% 2.85/1.51  #Tautology    : 64
% 2.85/1.51  #SimpNegUnit  : 3
% 2.85/1.51  #BackRed      : 7
% 2.85/1.51  
% 2.85/1.51  #Partial instantiations: 0
% 2.85/1.51  #Strategies tried      : 1
% 2.85/1.51  
% 2.85/1.51  Timing (in seconds)
% 2.85/1.51  ----------------------
% 2.85/1.51  Preprocessing        : 0.36
% 2.85/1.51  Parsing              : 0.20
% 2.85/1.51  CNF conversion       : 0.02
% 2.85/1.51  Main loop            : 0.33
% 2.85/1.51  Inferencing          : 0.12
% 2.85/1.51  Reduction            : 0.10
% 2.85/1.51  Demodulation         : 0.08
% 2.85/1.51  BG Simplification    : 0.02
% 2.85/1.51  Subsumption          : 0.06
% 2.85/1.51  Abstraction          : 0.02
% 2.85/1.51  MUC search           : 0.00
% 2.85/1.51  Cooper               : 0.00
% 2.85/1.51  Total                : 0.72
% 2.85/1.51  Index Insertion      : 0.00
% 2.85/1.51  Index Deletion       : 0.00
% 2.85/1.51  Index Matching       : 0.00
% 2.85/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
