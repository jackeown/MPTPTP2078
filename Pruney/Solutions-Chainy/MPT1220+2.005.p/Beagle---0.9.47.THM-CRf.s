%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 239 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  105 ( 390 expanded)
%              Number of equality atoms :   26 ( 137 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    ! [A_27] :
      ( k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [A_28] :
      ( k1_struct_0(A_28) = k1_xboole_0
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_68,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_132,plain,(
    ! [A_38] :
      ( k3_subset_1(u1_struct_0(A_38),k1_struct_0(A_38)) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_132])).

tff(c_144,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_147,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_144])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147])).

tff(c_153,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_28,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_221,plain,(
    ! [B_45,A_46] :
      ( k3_subset_1(B_45,k3_subset_1(B_45,A_46)) = A_46
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_22,c_175])).

tff(c_249,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_221])).

tff(c_270,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_249])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( k2_subset_1(A_8) = B_9
      | ~ r1_tarski(k3_subset_1(A_8,B_9),B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(k3_subset_1(A_8,B_9),B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_279,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ r1_tarski(k1_xboole_0,k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_43])).

tff(c_284,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_279])).

tff(c_306,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_326,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_306])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_326])).

tff(c_334,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_479,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k2_pre_topc(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_489,plain,(
    ! [B_59] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_59),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_479])).

tff(c_529,plain,(
    ! [B_61] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_61),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_334,c_489])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_540,plain,(
    ! [B_62] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_62),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_529,c_20])).

tff(c_36,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_411,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,k2_pre_topc(A_50,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_427,plain,(
    ! [A_51] :
      ( r1_tarski(u1_struct_0(A_51),k2_pre_topc(A_51,u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_41,c_411])).

tff(c_432,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_427])).

tff(c_438,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_334,c_432])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_442,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_445,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_442])).

tff(c_543,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_540,c_445])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.33  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.34/1.33  
% 2.34/1.33  %Foreground sorts:
% 2.34/1.33  
% 2.34/1.33  
% 2.34/1.33  %Background operators:
% 2.34/1.33  
% 2.34/1.33  
% 2.34/1.33  %Foreground operators:
% 2.34/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.34/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.33  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.34/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.34/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.34/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.34/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.33  
% 2.34/1.34  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.34/1.34  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.34/1.34  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.34/1.34  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.34/1.34  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.34/1.34  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.34/1.34  tff(f_65, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.34/1.34  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.34/1.34  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.34/1.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.34/1.34  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.34/1.34  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.34/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.34/1.34  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.34  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.34  tff(c_41, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.34/1.34  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.34/1.34  tff(c_30, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.34/1.34  tff(c_59, plain, (![A_27]: (k1_struct_0(A_27)=k1_xboole_0 | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.34/1.34  tff(c_64, plain, (![A_28]: (k1_struct_0(A_28)=k1_xboole_0 | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.34/1.34  tff(c_68, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.34/1.34  tff(c_132, plain, (![A_38]: (k3_subset_1(u1_struct_0(A_38), k1_struct_0(A_38))=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.34/1.34  tff(c_141, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_132])).
% 2.34/1.34  tff(c_144, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_141])).
% 2.34/1.34  tff(c_147, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_144])).
% 2.34/1.34  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_147])).
% 2.34/1.34  tff(c_153, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 2.34/1.34  tff(c_28, plain, (![A_15]: (m1_subset_1(k2_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.34  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.34  tff(c_152, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 2.34/1.34  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.34  tff(c_175, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.34  tff(c_221, plain, (![B_45, A_46]: (k3_subset_1(B_45, k3_subset_1(B_45, A_46))=A_46 | ~r1_tarski(A_46, B_45))), inference(resolution, [status(thm)], [c_22, c_175])).
% 2.34/1.34  tff(c_249, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_221])).
% 2.34/1.34  tff(c_270, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_249])).
% 2.34/1.34  tff(c_18, plain, (![A_8, B_9]: (k2_subset_1(A_8)=B_9 | ~r1_tarski(k3_subset_1(A_8, B_9), B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.34/1.34  tff(c_43, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(k3_subset_1(A_8, B_9), B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.34/1.34  tff(c_279, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~r1_tarski(k1_xboole_0, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_270, c_43])).
% 2.34/1.34  tff(c_284, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_279])).
% 2.34/1.34  tff(c_306, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_284])).
% 2.34/1.34  tff(c_326, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_306])).
% 2.34/1.34  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_326])).
% 2.34/1.34  tff(c_334, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_284])).
% 2.34/1.34  tff(c_479, plain, (![A_58, B_59]: (m1_subset_1(k2_pre_topc(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.34/1.34  tff(c_489, plain, (![B_59]: (m1_subset_1(k2_pre_topc('#skF_1', B_59), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_479])).
% 2.34/1.34  tff(c_529, plain, (![B_61]: (m1_subset_1(k2_pre_topc('#skF_1', B_61), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_334, c_489])).
% 2.34/1.34  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.34  tff(c_540, plain, (![B_62]: (r1_tarski(k2_pre_topc('#skF_1', B_62), k2_struct_0('#skF_1')) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_529, c_20])).
% 2.34/1.34  tff(c_36, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.34/1.34  tff(c_411, plain, (![B_49, A_50]: (r1_tarski(B_49, k2_pre_topc(A_50, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.34/1.34  tff(c_427, plain, (![A_51]: (r1_tarski(u1_struct_0(A_51), k2_pre_topc(A_51, u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_41, c_411])).
% 2.34/1.34  tff(c_432, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_334, c_427])).
% 2.34/1.34  tff(c_438, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_334, c_432])).
% 2.34/1.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.34  tff(c_442, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_438, c_2])).
% 2.34/1.34  tff(c_445, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_442])).
% 2.34/1.34  tff(c_543, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_540, c_445])).
% 2.34/1.34  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_543])).
% 2.34/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.34  
% 2.34/1.34  Inference rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Ref     : 0
% 2.34/1.34  #Sup     : 113
% 2.34/1.34  #Fact    : 0
% 2.34/1.34  #Define  : 0
% 2.34/1.34  #Split   : 4
% 2.34/1.34  #Chain   : 0
% 2.34/1.34  #Close   : 0
% 2.34/1.34  
% 2.34/1.34  Ordering : KBO
% 2.34/1.34  
% 2.34/1.34  Simplification rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Subsume      : 3
% 2.34/1.34  #Demod        : 78
% 2.34/1.34  #Tautology    : 67
% 2.34/1.34  #SimpNegUnit  : 1
% 2.34/1.34  #BackRed      : 3
% 2.34/1.34  
% 2.34/1.34  #Partial instantiations: 0
% 2.34/1.34  #Strategies tried      : 1
% 2.34/1.34  
% 2.34/1.34  Timing (in seconds)
% 2.34/1.34  ----------------------
% 2.34/1.34  Preprocessing        : 0.29
% 2.34/1.34  Parsing              : 0.17
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.28
% 2.34/1.35  Inferencing          : 0.11
% 2.34/1.35  Reduction            : 0.08
% 2.34/1.35  Demodulation         : 0.06
% 2.34/1.35  BG Simplification    : 0.01
% 2.34/1.35  Subsumption          : 0.06
% 2.34/1.35  Abstraction          : 0.01
% 2.34/1.35  MUC search           : 0.00
% 2.34/1.35  Cooper               : 0.00
% 2.34/1.35  Total                : 0.61
% 2.34/1.35  Index Insertion      : 0.00
% 2.34/1.35  Index Deletion       : 0.00
% 2.34/1.35  Index Matching       : 0.00
% 2.34/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
