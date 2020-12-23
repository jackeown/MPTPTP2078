%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 249 expanded)
%              Number of leaves         :   30 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 538 expanded)
%              Number of equality atoms :   26 ( 100 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & r1_tarski(B,C) )
                 => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_43,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_28])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_30])).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_45,c_94])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_64])).

tff(c_50,plain,(
    ! [A_31] :
      ( m1_subset_1(k2_struct_0(A_31),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_50])).

tff(c_54,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_57,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57])).

tff(c_62,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_123,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_subset_1(A_36,B_37,C_38) = k4_xboole_0(B_37,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [C_38] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_38) = k4_xboole_0(k2_struct_0('#skF_1'),C_38) ),
    inference(resolution,[status(thm)],[c_62,c_123])).

tff(c_266,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k7_subset_1(u1_struct_0(A_52),k2_struct_0(A_52),B_53)) = k7_subset_1(u1_struct_0(A_52),k2_struct_0(A_52),B_53)
      | ~ v3_pre_topc(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_278,plain,(
    ! [B_53] :
      ( k2_pre_topc('#skF_1',k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_53)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_53)
      | ~ v3_pre_topc(B_53,'#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_266])).

tff(c_283,plain,(
    ! [B_54] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_54)) = k4_xboole_0(k2_struct_0('#skF_1'),B_54)
      | ~ v3_pre_topc(B_54,'#skF_1')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43,c_132,c_132,c_43,c_278])).

tff(c_289,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_283])).

tff(c_297,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75,c_75,c_289])).

tff(c_163,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(u1_struct_0(A_42),k2_pre_topc(A_42,k3_subset_1(u1_struct_0(A_42),B_43))) = k1_tops_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,(
    ! [B_43] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_43))) = k1_tops_1('#skF_1',B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_163])).

tff(c_185,plain,(
    ! [B_43] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_43))) = k1_tops_1('#skF_1',B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43,c_43,c_178])).

tff(c_303,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_185])).

tff(c_307,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_105,c_303])).

tff(c_20,plain,(
    ! [A_17,B_21,C_23] :
      ( r1_tarski(k1_tops_1(A_17,B_21),k1_tops_1(A_17,C_23))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_325,plain,(
    ! [C_23] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',C_23))
      | ~ r1_tarski('#skF_2',C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_20])).

tff(c_338,plain,(
    ! [C_57] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',C_57))
      | ~ r1_tarski('#skF_2',C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_45,c_43,c_43,c_325])).

tff(c_347,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_338])).

tff(c_353,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_347])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.35  
% 2.66/1.35  %Foreground sorts:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Background operators:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Foreground operators:
% 2.66/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.66/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.66/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.35  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.66/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.66/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.66/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.35  
% 2.81/1.37  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.81/1.37  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.81/1.37  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.81/1.37  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.81/1.37  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.81/1.37  tff(f_45, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.81/1.37  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.81/1.37  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) => (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) & ((v2_pre_topc(A) & (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_pre_topc)).
% 2.81/1.37  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.81/1.37  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 2.81/1.37  tff(c_22, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.37  tff(c_34, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.37  tff(c_39, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_12, c_34])).
% 2.81/1.37  tff(c_43, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.81/1.37  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_28])).
% 2.81/1.37  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_45, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_30])).
% 2.81/1.37  tff(c_94, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.37  tff(c_105, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_45, c_94])).
% 2.81/1.37  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.37  tff(c_64, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k3_subset_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.37  tff(c_75, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_45, c_64])).
% 2.81/1.37  tff(c_50, plain, (![A_31]: (m1_subset_1(k2_struct_0(A_31), k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.37  tff(c_53, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_50])).
% 2.81/1.37  tff(c_54, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_53])).
% 2.81/1.37  tff(c_57, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_54])).
% 2.81/1.37  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_57])).
% 2.81/1.37  tff(c_62, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_53])).
% 2.81/1.37  tff(c_123, plain, (![A_36, B_37, C_38]: (k7_subset_1(A_36, B_37, C_38)=k4_xboole_0(B_37, C_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.37  tff(c_132, plain, (![C_38]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_38)=k4_xboole_0(k2_struct_0('#skF_1'), C_38))), inference(resolution, [status(thm)], [c_62, c_123])).
% 2.81/1.37  tff(c_266, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k7_subset_1(u1_struct_0(A_52), k2_struct_0(A_52), B_53))=k7_subset_1(u1_struct_0(A_52), k2_struct_0(A_52), B_53) | ~v3_pre_topc(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.37  tff(c_278, plain, (![B_53]: (k2_pre_topc('#skF_1', k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_53))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_53) | ~v3_pre_topc(B_53, '#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_266])).
% 2.81/1.37  tff(c_283, plain, (![B_54]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_54))=k4_xboole_0(k2_struct_0('#skF_1'), B_54) | ~v3_pre_topc(B_54, '#skF_1') | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_43, c_132, c_132, c_43, c_278])).
% 2.81/1.37  tff(c_289, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_45, c_283])).
% 2.81/1.37  tff(c_297, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75, c_75, c_289])).
% 2.81/1.37  tff(c_163, plain, (![A_42, B_43]: (k3_subset_1(u1_struct_0(A_42), k2_pre_topc(A_42, k3_subset_1(u1_struct_0(A_42), B_43)))=k1_tops_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.37  tff(c_178, plain, (![B_43]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_43)))=k1_tops_1('#skF_1', B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_163])).
% 2.81/1.37  tff(c_185, plain, (![B_43]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_43)))=k1_tops_1('#skF_1', B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_43, c_43, c_178])).
% 2.81/1.37  tff(c_303, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_297, c_185])).
% 2.81/1.37  tff(c_307, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_105, c_303])).
% 2.81/1.37  tff(c_20, plain, (![A_17, B_21, C_23]: (r1_tarski(k1_tops_1(A_17, B_21), k1_tops_1(A_17, C_23)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.37  tff(c_325, plain, (![C_23]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', C_23)) | ~r1_tarski('#skF_2', C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_20])).
% 2.81/1.37  tff(c_338, plain, (![C_57]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', C_57)) | ~r1_tarski('#skF_2', C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_45, c_43, c_43, c_325])).
% 2.81/1.37  tff(c_347, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_338])).
% 2.81/1.37  tff(c_353, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_347])).
% 2.81/1.37  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_353])).
% 2.81/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  Inference rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Ref     : 0
% 2.81/1.37  #Sup     : 81
% 2.81/1.37  #Fact    : 0
% 2.81/1.37  #Define  : 0
% 2.81/1.37  #Split   : 6
% 2.81/1.37  #Chain   : 0
% 2.81/1.37  #Close   : 0
% 2.81/1.37  
% 2.81/1.37  Ordering : KBO
% 2.81/1.37  
% 2.81/1.37  Simplification rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Subsume      : 1
% 2.81/1.37  #Demod        : 50
% 2.81/1.37  #Tautology    : 43
% 2.81/1.37  #SimpNegUnit  : 1
% 2.81/1.37  #BackRed      : 2
% 2.81/1.37  
% 2.81/1.37  #Partial instantiations: 0
% 2.81/1.37  #Strategies tried      : 1
% 2.81/1.37  
% 2.81/1.37  Timing (in seconds)
% 2.81/1.37  ----------------------
% 2.81/1.37  Preprocessing        : 0.34
% 2.81/1.37  Parsing              : 0.18
% 2.81/1.37  CNF conversion       : 0.02
% 2.81/1.37  Main loop            : 0.26
% 2.81/1.37  Inferencing          : 0.10
% 2.81/1.37  Reduction            : 0.08
% 2.81/1.37  Demodulation         : 0.06
% 2.81/1.37  BG Simplification    : 0.02
% 2.81/1.37  Subsumption          : 0.04
% 2.81/1.37  Abstraction          : 0.02
% 2.81/1.37  MUC search           : 0.00
% 2.81/1.37  Cooper               : 0.00
% 2.81/1.37  Total                : 0.64
% 2.81/1.37  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
