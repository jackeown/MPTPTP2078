%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 21.47s
% Output     : CNFRefutation 21.47s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 131 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 252 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_62,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_64,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4634,plain,(
    ! [A_249,C_250,B_251] :
      ( r1_tarski(k2_pre_topc(A_249,C_250),B_251)
      | ~ r1_tarski(C_250,B_251)
      | ~ v4_pre_topc(B_251,A_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4647,plain,(
    ! [B_251] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_251)
      | ~ r1_tarski('#skF_2',B_251)
      | ~ v4_pre_topc(B_251,'#skF_1')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4634])).

tff(c_28566,plain,(
    ! [B_512] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_512)
      | ~ r1_tarski('#skF_2',B_512)
      | ~ v4_pre_topc(B_512,'#skF_1')
      | ~ m1_subset_1(B_512,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4647])).

tff(c_28585,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_28566])).

tff(c_28594,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_28585])).

tff(c_3848,plain,(
    ! [A_234,B_235] :
      ( k4_subset_1(u1_struct_0(A_234),B_235,k2_tops_1(A_234,B_235)) = k2_pre_topc(A_234,B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3861,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3848])).

tff(c_3868,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3861])).

tff(c_54,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k2_tops_1(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2679,plain,(
    ! [A_199,B_200,C_201] :
      ( k4_subset_1(A_199,B_200,C_201) = k2_xboole_0(B_200,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37729,plain,(
    ! [A_589,B_590,B_591] :
      ( k4_subset_1(u1_struct_0(A_589),B_590,k2_tops_1(A_589,B_591)) = k2_xboole_0(B_590,k2_tops_1(A_589,B_591))
      | ~ m1_subset_1(B_590,k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ m1_subset_1(B_591,k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ l1_pre_topc(A_589) ) ),
    inference(resolution,[status(thm)],[c_54,c_2679])).

tff(c_37742,plain,(
    ! [B_591] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_591)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_591))
      | ~ m1_subset_1(B_591,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_37729])).

tff(c_82782,plain,(
    ! [B_849] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_849)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_849))
      | ~ m1_subset_1(B_849,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_37742])).

tff(c_82805,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_82782])).

tff(c_82814,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3868,c_82805])).

tff(c_30,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_461,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_473,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(k2_xboole_0(A_26,B_27),A_26) ) ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_82962,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82814,c_473])).

tff(c_83054,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28594,c_82814,c_82962])).

tff(c_83060,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83054,c_82814])).

tff(c_32,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,A_28) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_814,plain,(
    ! [B_123,A_124] : k3_tarski(k2_tarski(B_123,A_124)) = k2_xboole_0(A_124,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_34,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_837,plain,(
    ! [B_125,A_126] : k2_xboole_0(B_125,A_126) = k2_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_34])).

tff(c_898,plain,(
    ! [A_126,B_125] : r1_tarski(A_126,k2_xboole_0(B_125,A_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_30])).

tff(c_83649,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83060,c_898])).

tff(c_83704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_83649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.47/12.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.47/12.82  
% 21.47/12.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.47/12.82  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 21.47/12.82  
% 21.47/12.82  %Foreground sorts:
% 21.47/12.82  
% 21.47/12.82  
% 21.47/12.82  %Background operators:
% 21.47/12.82  
% 21.47/12.82  
% 21.47/12.82  %Foreground operators:
% 21.47/12.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.47/12.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.47/12.82  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 21.47/12.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.47/12.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.47/12.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.47/12.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.47/12.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.47/12.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.47/12.82  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 21.47/12.82  tff('#skF_2', type, '#skF_2': $i).
% 21.47/12.82  tff('#skF_1', type, '#skF_1': $i).
% 21.47/12.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.47/12.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.47/12.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.47/12.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 21.47/12.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.47/12.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.47/12.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.47/12.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.47/12.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 21.47/12.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.47/12.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.47/12.82  
% 21.47/12.83  tff(f_155, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 21.47/12.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.47/12.83  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 21.47/12.83  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 21.47/12.83  tff(f_117, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 21.47/12.83  tff(f_89, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 21.47/12.83  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 21.47/12.83  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 21.47/12.83  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 21.47/12.83  tff(c_62, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.47/12.83  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.47/12.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.47/12.83  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.47/12.83  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 21.47/12.83  tff(c_4634, plain, (![A_249, C_250, B_251]: (r1_tarski(k2_pre_topc(A_249, C_250), B_251) | ~r1_tarski(C_250, B_251) | ~v4_pre_topc(B_251, A_249) | ~m1_subset_1(C_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_131])).
% 21.47/12.83  tff(c_4647, plain, (![B_251]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_251) | ~r1_tarski('#skF_2', B_251) | ~v4_pre_topc(B_251, '#skF_1') | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4634])).
% 21.47/12.83  tff(c_28566, plain, (![B_512]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_512) | ~r1_tarski('#skF_2', B_512) | ~v4_pre_topc(B_512, '#skF_1') | ~m1_subset_1(B_512, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4647])).
% 21.47/12.83  tff(c_28585, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_28566])).
% 21.47/12.83  tff(c_28594, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_28585])).
% 21.47/12.83  tff(c_3848, plain, (![A_234, B_235]: (k4_subset_1(u1_struct_0(A_234), B_235, k2_tops_1(A_234, B_235))=k2_pre_topc(A_234, B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_145])).
% 21.47/12.83  tff(c_3861, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_3848])).
% 21.47/12.83  tff(c_3868, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3861])).
% 21.47/12.83  tff(c_54, plain, (![A_54, B_55]: (m1_subset_1(k2_tops_1(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_117])).
% 21.47/12.83  tff(c_2679, plain, (![A_199, B_200, C_201]: (k4_subset_1(A_199, B_200, C_201)=k2_xboole_0(B_200, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(A_199)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.47/12.83  tff(c_37729, plain, (![A_589, B_590, B_591]: (k4_subset_1(u1_struct_0(A_589), B_590, k2_tops_1(A_589, B_591))=k2_xboole_0(B_590, k2_tops_1(A_589, B_591)) | ~m1_subset_1(B_590, k1_zfmisc_1(u1_struct_0(A_589))) | ~m1_subset_1(B_591, k1_zfmisc_1(u1_struct_0(A_589))) | ~l1_pre_topc(A_589))), inference(resolution, [status(thm)], [c_54, c_2679])).
% 21.47/12.83  tff(c_37742, plain, (![B_591]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_591))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_591)) | ~m1_subset_1(B_591, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_37729])).
% 21.47/12.83  tff(c_82782, plain, (![B_849]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_849))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_849)) | ~m1_subset_1(B_849, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_37742])).
% 21.47/12.83  tff(c_82805, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_82782])).
% 21.47/12.83  tff(c_82814, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3868, c_82805])).
% 21.47/12.83  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.47/12.83  tff(c_461, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.47/12.83  tff(c_473, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(k2_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_30, c_461])).
% 21.47/12.83  tff(c_82962, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82814, c_473])).
% 21.47/12.83  tff(c_83054, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28594, c_82814, c_82962])).
% 21.47/12.83  tff(c_83060, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83054, c_82814])).
% 21.47/12.83  tff(c_32, plain, (![B_29, A_28]: (k2_tarski(B_29, A_28)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.47/12.83  tff(c_133, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.47/12.83  tff(c_814, plain, (![B_123, A_124]: (k3_tarski(k2_tarski(B_123, A_124))=k2_xboole_0(A_124, B_123))), inference(superposition, [status(thm), theory('equality')], [c_32, c_133])).
% 21.47/12.83  tff(c_34, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.47/12.83  tff(c_837, plain, (![B_125, A_126]: (k2_xboole_0(B_125, A_126)=k2_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_814, c_34])).
% 21.47/12.83  tff(c_898, plain, (![A_126, B_125]: (r1_tarski(A_126, k2_xboole_0(B_125, A_126)))), inference(superposition, [status(thm), theory('equality')], [c_837, c_30])).
% 21.47/12.83  tff(c_83649, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83060, c_898])).
% 21.47/12.83  tff(c_83704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_83649])).
% 21.47/12.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.47/12.83  
% 21.47/12.83  Inference rules
% 21.47/12.83  ----------------------
% 21.47/12.83  #Ref     : 0
% 21.47/12.83  #Sup     : 20418
% 21.47/12.83  #Fact    : 0
% 21.47/12.83  #Define  : 0
% 21.47/12.83  #Split   : 4
% 21.47/12.83  #Chain   : 0
% 21.47/12.83  #Close   : 0
% 21.47/12.83  
% 21.47/12.83  Ordering : KBO
% 21.47/12.83  
% 21.47/12.83  Simplification rules
% 21.47/12.83  ----------------------
% 21.47/12.83  #Subsume      : 1184
% 21.47/12.83  #Demod        : 20757
% 21.47/12.83  #Tautology    : 13315
% 21.47/12.83  #SimpNegUnit  : 29
% 21.47/12.83  #BackRed      : 53
% 21.47/12.83  
% 21.47/12.83  #Partial instantiations: 0
% 21.47/12.83  #Strategies tried      : 1
% 21.47/12.83  
% 21.47/12.83  Timing (in seconds)
% 21.47/12.83  ----------------------
% 21.47/12.83  Preprocessing        : 0.43
% 21.47/12.83  Parsing              : 0.25
% 21.47/12.83  CNF conversion       : 0.03
% 21.47/12.83  Main loop            : 11.53
% 21.47/12.83  Inferencing          : 1.42
% 21.47/12.83  Reduction            : 7.03
% 21.47/12.83  Demodulation         : 6.31
% 21.47/12.83  BG Simplification    : 0.15
% 21.47/12.83  Subsumption          : 2.45
% 21.47/12.83  Abstraction          : 0.27
% 21.47/12.83  MUC search           : 0.00
% 21.47/12.83  Cooper               : 0.00
% 21.47/12.84  Total                : 12.00
% 21.47/12.84  Index Insertion      : 0.00
% 21.47/12.84  Index Deletion       : 0.00
% 21.47/12.84  Index Matching       : 0.00
% 21.47/12.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
