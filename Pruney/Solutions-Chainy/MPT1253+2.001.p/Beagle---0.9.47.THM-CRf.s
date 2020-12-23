%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 23.34s
% Output     : CNFRefutation 23.48s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 124 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 247 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_155,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_68,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5946,plain,(
    ! [A_279,C_280,B_281] :
      ( r1_tarski(k2_pre_topc(A_279,C_280),B_281)
      | ~ r1_tarski(C_280,B_281)
      | ~ v4_pre_topc(B_281,A_279)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5959,plain,(
    ! [B_281] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_281)
      | ~ r1_tarski('#skF_3',B_281)
      | ~ v4_pre_topc(B_281,'#skF_2')
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_5946])).

tff(c_6105,plain,(
    ! [B_287] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_287)
      | ~ r1_tarski('#skF_3',B_287)
      | ~ v4_pre_topc(B_287,'#skF_2')
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5959])).

tff(c_6124,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_6105])).

tff(c_6133,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14,c_6124])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6143,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6133,c_10])).

tff(c_6479,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6143])).

tff(c_3799,plain,(
    ! [A_232,B_233] :
      ( k4_subset_1(u1_struct_0(A_232),B_233,k2_tops_1(A_232,B_233)) = k2_pre_topc(A_232,B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3812,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_3799])).

tff(c_3819,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3812])).

tff(c_60,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k2_tops_1(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3266,plain,(
    ! [A_220,B_221,C_222] :
      ( k4_subset_1(A_220,B_221,C_222) = k2_xboole_0(B_221,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(A_220))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_33637,plain,(
    ! [A_579,B_580,B_581] :
      ( k4_subset_1(u1_struct_0(A_579),B_580,k2_tops_1(A_579,B_581)) = k2_xboole_0(B_580,k2_tops_1(A_579,B_581))
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ l1_pre_topc(A_579) ) ),
    inference(resolution,[status(thm)],[c_60,c_3266])).

tff(c_33656,plain,(
    ! [B_581] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_581)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_581))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_33637])).

tff(c_63304,plain,(
    ! [B_753] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_753)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_753))
      | ~ m1_subset_1(B_753,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_33656])).

tff(c_63334,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_63304])).

tff(c_63347,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3819,c_63334])).

tff(c_36,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63574,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_63347,c_36])).

tff(c_63610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6479,c_63574])).

tff(c_63611,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6143])).

tff(c_63618,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63611,c_3819])).

tff(c_90930,plain,(
    ! [A_1047,B_1048,B_1049] :
      ( k4_subset_1(u1_struct_0(A_1047),B_1048,k2_tops_1(A_1047,B_1049)) = k2_xboole_0(B_1048,k2_tops_1(A_1047,B_1049))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(A_1047)))
      | ~ m1_subset_1(B_1049,k1_zfmisc_1(u1_struct_0(A_1047)))
      | ~ l1_pre_topc(A_1047) ) ),
    inference(resolution,[status(thm)],[c_60,c_3266])).

tff(c_90949,plain,(
    ! [B_1049] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_1049)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_1049))
      | ~ m1_subset_1(B_1049,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_90930])).

tff(c_116584,plain,(
    ! [B_1220] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_1220)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_1220))
      | ~ m1_subset_1(B_1220,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_90949])).

tff(c_116614,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_116584])).

tff(c_116627,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63618,c_116614])).

tff(c_158,plain,(
    ! [B_87,A_88] : k2_xboole_0(B_87,A_88) = k2_xboole_0(A_88,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_173,plain,(
    ! [A_88,B_87] : r1_tarski(A_88,k2_xboole_0(B_87,A_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_36])).

tff(c_116851,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116627,c_173])).

tff(c_116907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_116851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:08:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.34/15.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.34/15.17  
% 23.34/15.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.34/15.17  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 23.34/15.17  
% 23.34/15.17  %Foreground sorts:
% 23.34/15.17  
% 23.34/15.17  
% 23.34/15.17  %Background operators:
% 23.34/15.17  
% 23.34/15.17  
% 23.34/15.17  %Foreground operators:
% 23.34/15.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.34/15.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.34/15.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.34/15.17  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.34/15.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.34/15.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.34/15.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.34/15.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.34/15.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.34/15.17  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.34/15.17  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.34/15.17  tff('#skF_2', type, '#skF_2': $i).
% 23.34/15.17  tff('#skF_3', type, '#skF_3': $i).
% 23.34/15.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.34/15.17  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.34/15.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.34/15.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.34/15.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.34/15.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.34/15.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.34/15.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 23.34/15.17  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.34/15.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.34/15.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.34/15.17  
% 23.48/15.19  tff(f_165, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 23.48/15.19  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.48/15.19  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 23.48/15.19  tff(f_155, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 23.48/15.19  tff(f_127, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 23.48/15.19  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.48/15.19  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 23.48/15.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 23.48/15.19  tff(c_68, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.48/15.19  tff(c_70, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.48/15.19  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.48/15.19  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.48/15.19  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 23.48/15.19  tff(c_5946, plain, (![A_279, C_280, B_281]: (r1_tarski(k2_pre_topc(A_279, C_280), B_281) | ~r1_tarski(C_280, B_281) | ~v4_pre_topc(B_281, A_279) | ~m1_subset_1(C_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_141])).
% 23.48/15.19  tff(c_5959, plain, (![B_281]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_281) | ~r1_tarski('#skF_3', B_281) | ~v4_pre_topc(B_281, '#skF_2') | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_5946])).
% 23.48/15.19  tff(c_6105, plain, (![B_287]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_287) | ~r1_tarski('#skF_3', B_287) | ~v4_pre_topc(B_287, '#skF_2') | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5959])).
% 23.48/15.19  tff(c_6124, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_6105])).
% 23.48/15.19  tff(c_6133, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14, c_6124])).
% 23.48/15.19  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.48/15.19  tff(c_6143, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6133, c_10])).
% 23.48/15.19  tff(c_6479, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6143])).
% 23.48/15.19  tff(c_3799, plain, (![A_232, B_233]: (k4_subset_1(u1_struct_0(A_232), B_233, k2_tops_1(A_232, B_233))=k2_pre_topc(A_232, B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_155])).
% 23.48/15.19  tff(c_3812, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_3799])).
% 23.48/15.19  tff(c_3819, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3812])).
% 23.48/15.19  tff(c_60, plain, (![A_58, B_59]: (m1_subset_1(k2_tops_1(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_127])).
% 23.48/15.19  tff(c_3266, plain, (![A_220, B_221, C_222]: (k4_subset_1(A_220, B_221, C_222)=k2_xboole_0(B_221, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(A_220)) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 23.48/15.19  tff(c_33637, plain, (![A_579, B_580, B_581]: (k4_subset_1(u1_struct_0(A_579), B_580, k2_tops_1(A_579, B_581))=k2_xboole_0(B_580, k2_tops_1(A_579, B_581)) | ~m1_subset_1(B_580, k1_zfmisc_1(u1_struct_0(A_579))) | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0(A_579))) | ~l1_pre_topc(A_579))), inference(resolution, [status(thm)], [c_60, c_3266])).
% 23.48/15.19  tff(c_33656, plain, (![B_581]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_581))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_581)) | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_33637])).
% 23.48/15.19  tff(c_63304, plain, (![B_753]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_753))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_753)) | ~m1_subset_1(B_753, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_33656])).
% 23.48/15.19  tff(c_63334, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_63304])).
% 23.48/15.19  tff(c_63347, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3819, c_63334])).
% 23.48/15.19  tff(c_36, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 23.48/15.19  tff(c_63574, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63347, c_36])).
% 23.48/15.19  tff(c_63610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6479, c_63574])).
% 23.48/15.19  tff(c_63611, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_6143])).
% 23.48/15.19  tff(c_63618, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63611, c_3819])).
% 23.48/15.19  tff(c_90930, plain, (![A_1047, B_1048, B_1049]: (k4_subset_1(u1_struct_0(A_1047), B_1048, k2_tops_1(A_1047, B_1049))=k2_xboole_0(B_1048, k2_tops_1(A_1047, B_1049)) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(A_1047))) | ~m1_subset_1(B_1049, k1_zfmisc_1(u1_struct_0(A_1047))) | ~l1_pre_topc(A_1047))), inference(resolution, [status(thm)], [c_60, c_3266])).
% 23.48/15.19  tff(c_90949, plain, (![B_1049]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_1049))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_1049)) | ~m1_subset_1(B_1049, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_90930])).
% 23.48/15.19  tff(c_116584, plain, (![B_1220]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_1220))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_1220)) | ~m1_subset_1(B_1220, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_90949])).
% 23.48/15.19  tff(c_116614, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_116584])).
% 23.48/15.19  tff(c_116627, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63618, c_116614])).
% 23.48/15.19  tff(c_158, plain, (![B_87, A_88]: (k2_xboole_0(B_87, A_88)=k2_xboole_0(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.48/15.19  tff(c_173, plain, (![A_88, B_87]: (r1_tarski(A_88, k2_xboole_0(B_87, A_88)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_36])).
% 23.48/15.19  tff(c_116851, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116627, c_173])).
% 23.48/15.19  tff(c_116907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_116851])).
% 23.48/15.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.48/15.19  
% 23.48/15.19  Inference rules
% 23.48/15.19  ----------------------
% 23.48/15.19  #Ref     : 0
% 23.48/15.19  #Sup     : 28505
% 23.48/15.19  #Fact    : 0
% 23.48/15.19  #Define  : 0
% 23.48/15.19  #Split   : 5
% 23.48/15.19  #Chain   : 0
% 23.48/15.19  #Close   : 0
% 23.48/15.19  
% 23.48/15.19  Ordering : KBO
% 23.48/15.19  
% 23.48/15.19  Simplification rules
% 23.48/15.19  ----------------------
% 23.48/15.19  #Subsume      : 1794
% 23.48/15.19  #Demod        : 28181
% 23.48/15.19  #Tautology    : 19109
% 23.48/15.19  #SimpNegUnit  : 3
% 23.48/15.19  #BackRed      : 10
% 23.48/15.19  
% 23.48/15.19  #Partial instantiations: 0
% 23.48/15.19  #Strategies tried      : 1
% 23.48/15.19  
% 23.48/15.19  Timing (in seconds)
% 23.48/15.19  ----------------------
% 23.48/15.19  Preprocessing        : 0.34
% 23.48/15.19  Parsing              : 0.18
% 23.48/15.19  CNF conversion       : 0.02
% 23.48/15.19  Main loop            : 14.09
% 23.48/15.19  Inferencing          : 1.76
% 23.48/15.19  Reduction            : 8.40
% 23.48/15.19  Demodulation         : 7.55
% 23.48/15.19  BG Simplification    : 0.19
% 23.48/15.19  Subsumption          : 3.20
% 23.48/15.19  Abstraction          : 0.34
% 23.48/15.19  MUC search           : 0.00
% 23.48/15.19  Cooper               : 0.00
% 23.48/15.19  Total                : 14.47
% 23.48/15.19  Index Insertion      : 0.00
% 23.48/15.19  Index Deletion       : 0.00
% 23.48/15.19  Index Matching       : 0.00
% 23.48/15.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
