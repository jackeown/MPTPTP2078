%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 183 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 428 expanded)
%              Number of equality atoms :   30 (  89 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_401,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = B_69
      | ~ v4_pre_topc(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_423,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_401])).

tff(c_442,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_423])).

tff(c_196,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,k2_pre_topc(A_60,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_211,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_196])).

tff(c_230,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_211])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_236,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_347,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_443,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_347])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_443])).

tff(c_448,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_108,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_3') = k3_xboole_0(B_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_28,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_288,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,B_64) = B_64
      | ~ v4_pre_topc(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_307,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_288])).

tff(c_326,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_307])).

tff(c_209,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_196])).

tff(c_227,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_209])).

tff(c_233,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_237,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_330,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_237])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_330])).

tff(c_336,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_115,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_26])).

tff(c_339,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_3') != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_115])).

tff(c_341,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_3') != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_339])).

tff(c_457,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_341])).

tff(c_8,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_134,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k7_subset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [C_44] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_44),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_134])).

tff(c_151,plain,(
    ! [C_55] : m1_subset_1(k4_xboole_0('#skF_2',C_55),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_141])).

tff(c_163,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_200,plain,(
    ! [B_4] :
      ( r1_tarski(k3_xboole_0('#skF_2',B_4),k2_pre_topc('#skF_1',k3_xboole_0('#skF_2',B_4)))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_163,c_196])).

tff(c_217,plain,(
    ! [B_4] : r1_tarski(k3_xboole_0('#skF_2',B_4),k2_pre_topc('#skF_1',k3_xboole_0('#skF_2',B_4))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_200])).

tff(c_1019,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(k2_pre_topc(A_100,k9_subset_1(u1_struct_0(A_100),B_101,C_102)),k9_subset_1(u1_struct_0(A_100),k2_pre_topc(A_100,B_101),k2_pre_topc(A_100,C_102)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1042,plain,(
    ! [B_48] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_48,'#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_48),k2_pre_topc('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1019])).

tff(c_1250,plain,(
    ! [B_112] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_112,'#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1',B_112),'#skF_3'))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_113,c_336,c_1042])).

tff(c_1261,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_1250])).

tff(c_1271,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1261])).

tff(c_1275,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1271,c_2])).

tff(c_1278,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_1275])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_1278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.14/1.50  
% 3.14/1.50  %Foreground sorts:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Background operators:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Foreground operators:
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.50  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.14/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.14/1.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.14/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.50  
% 3.29/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.51  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_1)).
% 3.29/1.51  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.29/1.51  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.29/1.51  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.29/1.51  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.29/1.51  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.29/1.51  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.29/1.51  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 3.29/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.51  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_30, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_401, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=B_69 | ~v4_pre_topc(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.51  tff(c_423, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_401])).
% 3.29/1.51  tff(c_442, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_423])).
% 3.29/1.51  tff(c_196, plain, (![B_59, A_60]: (r1_tarski(B_59, k2_pre_topc(A_60, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.29/1.51  tff(c_211, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_196])).
% 3.29/1.51  tff(c_230, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_211])).
% 3.29/1.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.51  tff(c_236, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_230, c_2])).
% 3.29/1.51  tff(c_347, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_236])).
% 3.29/1.51  tff(c_443, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_347])).
% 3.29/1.51  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_443])).
% 3.29/1.51  tff(c_448, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_236])).
% 3.29/1.51  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_108, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, C_49)=k3_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.51  tff(c_113, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_3')=k3_xboole_0(B_48, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_108])).
% 3.29/1.51  tff(c_28, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_288, plain, (![A_63, B_64]: (k2_pre_topc(A_63, B_64)=B_64 | ~v4_pre_topc(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.51  tff(c_307, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_288])).
% 3.29/1.51  tff(c_326, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_307])).
% 3.29/1.51  tff(c_209, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_196])).
% 3.29/1.51  tff(c_227, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_209])).
% 3.29/1.51  tff(c_233, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_227, c_2])).
% 3.29/1.51  tff(c_237, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_233])).
% 3.29/1.51  tff(c_330, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_237])).
% 3.29/1.51  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_330])).
% 3.29/1.51  tff(c_336, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_233])).
% 3.29/1.51  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.51  tff(c_115, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_26])).
% 3.29/1.51  tff(c_339, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_115])).
% 3.29/1.51  tff(c_341, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_339])).
% 3.29/1.51  tff(c_457, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_341])).
% 3.29/1.51  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.51  tff(c_83, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.51  tff(c_89, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_34, c_83])).
% 3.29/1.51  tff(c_134, plain, (![A_52, B_53, C_54]: (m1_subset_1(k7_subset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.51  tff(c_141, plain, (![C_44]: (m1_subset_1(k4_xboole_0('#skF_2', C_44), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_89, c_134])).
% 3.29/1.51  tff(c_151, plain, (![C_55]: (m1_subset_1(k4_xboole_0('#skF_2', C_55), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_141])).
% 3.29/1.51  tff(c_163, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_151])).
% 3.29/1.51  tff(c_200, plain, (![B_4]: (r1_tarski(k3_xboole_0('#skF_2', B_4), k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', B_4))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_163, c_196])).
% 3.29/1.51  tff(c_217, plain, (![B_4]: (r1_tarski(k3_xboole_0('#skF_2', B_4), k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', B_4))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_200])).
% 3.29/1.51  tff(c_1019, plain, (![A_100, B_101, C_102]: (r1_tarski(k2_pre_topc(A_100, k9_subset_1(u1_struct_0(A_100), B_101, C_102)), k9_subset_1(u1_struct_0(A_100), k2_pre_topc(A_100, B_101), k2_pre_topc(A_100, C_102))) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.51  tff(c_1042, plain, (![B_48]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_48, '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_48), k2_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1019])).
% 3.29/1.51  tff(c_1250, plain, (![B_112]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_112, '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', B_112), '#skF_3')) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_113, c_336, c_1042])).
% 3.29/1.51  tff(c_1261, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_448, c_1250])).
% 3.29/1.51  tff(c_1271, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1261])).
% 3.29/1.51  tff(c_1275, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_1271, c_2])).
% 3.29/1.51  tff(c_1278, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_1275])).
% 3.29/1.51  tff(c_1280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_1278])).
% 3.29/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  Inference rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Ref     : 0
% 3.29/1.51  #Sup     : 262
% 3.29/1.51  #Fact    : 0
% 3.29/1.51  #Define  : 0
% 3.29/1.51  #Split   : 3
% 3.29/1.51  #Chain   : 0
% 3.29/1.51  #Close   : 0
% 3.29/1.51  
% 3.29/1.51  Ordering : KBO
% 3.29/1.51  
% 3.29/1.51  Simplification rules
% 3.29/1.52  ----------------------
% 3.29/1.52  #Subsume      : 0
% 3.29/1.52  #Demod        : 234
% 3.29/1.52  #Tautology    : 80
% 3.29/1.52  #SimpNegUnit  : 1
% 3.29/1.52  #BackRed      : 11
% 3.29/1.52  
% 3.29/1.52  #Partial instantiations: 0
% 3.29/1.52  #Strategies tried      : 1
% 3.29/1.52  
% 3.29/1.52  Timing (in seconds)
% 3.29/1.52  ----------------------
% 3.29/1.52  Preprocessing        : 0.31
% 3.29/1.52  Parsing              : 0.17
% 3.29/1.52  CNF conversion       : 0.02
% 3.29/1.52  Main loop            : 0.41
% 3.29/1.52  Inferencing          : 0.13
% 3.29/1.52  Reduction            : 0.16
% 3.29/1.52  Demodulation         : 0.12
% 3.29/1.52  BG Simplification    : 0.02
% 3.29/1.52  Subsumption          : 0.06
% 3.29/1.52  Abstraction          : 0.03
% 3.29/1.52  MUC search           : 0.00
% 3.29/1.52  Cooper               : 0.00
% 3.29/1.52  Total                : 0.76
% 3.29/1.52  Index Insertion      : 0.00
% 3.29/1.52  Index Deletion       : 0.00
% 3.29/1.52  Index Matching       : 0.00
% 3.29/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
