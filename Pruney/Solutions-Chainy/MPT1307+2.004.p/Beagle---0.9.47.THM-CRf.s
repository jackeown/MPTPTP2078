%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 12.98s
% Output     : CNFRefutation 12.98s
% Verified   : 
% Statistics : Number of formulae       :   64 (  79 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 149 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k5_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_107,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(A_75,C_76)
      | ~ r1_tarski(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_57,c_107])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_193,plain,(
    ! [A_95,A_96] :
      ( r1_tarski(A_95,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_95,A_96)
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_120,c_14])).

tff(c_11432,plain,(
    ! [A_769,C_770,B_771] :
      ( r1_tarski(k5_xboole_0(A_769,C_770),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_771,'#skF_2')
      | ~ r1_tarski(C_770,B_771)
      | ~ r1_tarski(A_769,B_771) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_11504,plain,(
    ! [A_769,C_770] :
      ( r1_tarski(k5_xboole_0(A_769,C_770),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(C_770,'#skF_2')
      | ~ r1_tarski(A_769,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_11432])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1099,plain,(
    ! [B_214,A_215,C_216] :
      ( v2_tops_2(B_214,A_215)
      | ~ v2_tops_2(C_216,A_215)
      | ~ r1_tarski(B_214,C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2254,plain,(
    ! [A_332,C_333,A_334,B_335] :
      ( v2_tops_2(k5_xboole_0(A_332,C_333),A_334)
      | ~ v2_tops_2(B_335,A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_334))))
      | ~ m1_subset_1(k5_xboole_0(A_332,C_333),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_334))))
      | ~ l1_pre_topc(A_334)
      | ~ r1_tarski(C_333,B_335)
      | ~ r1_tarski(A_332,B_335) ) ),
    inference(resolution,[status(thm)],[c_12,c_1099])).

tff(c_2261,plain,(
    ! [A_332,C_333] :
      ( v2_tops_2(k5_xboole_0(A_332,C_333),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1(k5_xboole_0(A_332,C_333),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(C_333,'#skF_2')
      | ~ r1_tarski(A_332,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_2254])).

tff(c_2310,plain,(
    ! [A_340,C_341] :
      ( v2_tops_2(k5_xboole_0(A_340,C_341),'#skF_1')
      | ~ m1_subset_1(k5_xboole_0(A_340,C_341),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(C_341,'#skF_2')
      | ~ r1_tarski(A_340,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_2261])).

tff(c_17039,plain,(
    ! [A_927,C_928] :
      ( v2_tops_2(k5_xboole_0(A_927,C_928),'#skF_1')
      | ~ r1_tarski(C_928,'#skF_2')
      | ~ r1_tarski(A_927,'#skF_2')
      | ~ r1_tarski(k5_xboole_0(A_927,C_928),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2310])).

tff(c_17099,plain,(
    ! [A_929,C_930] :
      ( v2_tops_2(k5_xboole_0(A_929,C_930),'#skF_1')
      | ~ r1_tarski(C_930,'#skF_2')
      | ~ r1_tarski(A_929,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_11504,c_17039])).

tff(c_24405,plain,(
    ! [A_1080,B_1081] :
      ( v2_tops_2(k4_xboole_0(A_1080,B_1081),'#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_1080,B_1081),'#skF_2')
      | ~ r1_tarski(A_1080,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_17099])).

tff(c_155,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_164,plain,(
    ! [C_88] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_44,c_155])).

tff(c_38,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_183,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_38])).

tff(c_24408,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_24405,c_183])).

tff(c_24411,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24408])).

tff(c_24414,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_24411])).

tff(c_24418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.98/6.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/6.27  
% 12.98/6.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/6.28  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 12.98/6.28  
% 12.98/6.28  %Foreground sorts:
% 12.98/6.28  
% 12.98/6.28  
% 12.98/6.28  %Background operators:
% 12.98/6.28  
% 12.98/6.28  
% 12.98/6.28  %Foreground operators:
% 12.98/6.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.98/6.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.98/6.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.98/6.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.98/6.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.98/6.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.98/6.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.98/6.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.98/6.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.98/6.28  tff('#skF_2', type, '#skF_2': $i).
% 12.98/6.28  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.98/6.28  tff('#skF_3', type, '#skF_3': $i).
% 12.98/6.28  tff('#skF_1', type, '#skF_1': $i).
% 12.98/6.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.98/6.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.98/6.28  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 12.98/6.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.98/6.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.98/6.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.98/6.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.98/6.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.98/6.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.98/6.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.98/6.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.98/6.28  
% 12.98/6.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.98/6.29  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 12.98/6.29  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.98/6.29  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 12.98/6.29  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tops_2)).
% 12.98/6.29  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.98/6.29  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.98/6.29  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 12.98/6.29  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.98/6.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/6.29  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.98/6.29  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.98/6.29  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k5_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.98/6.29  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.98/6.29  tff(c_49, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.98/6.29  tff(c_57, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_49])).
% 12.98/6.29  tff(c_107, plain, (![A_75, C_76, B_77]: (r1_tarski(A_75, C_76) | ~r1_tarski(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.98/6.29  tff(c_120, plain, (![A_78]: (r1_tarski(A_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_78, '#skF_2'))), inference(resolution, [status(thm)], [c_57, c_107])).
% 12.98/6.29  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.98/6.29  tff(c_193, plain, (![A_95, A_96]: (r1_tarski(A_95, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_95, A_96) | ~r1_tarski(A_96, '#skF_2'))), inference(resolution, [status(thm)], [c_120, c_14])).
% 12.98/6.29  tff(c_11432, plain, (![A_769, C_770, B_771]: (r1_tarski(k5_xboole_0(A_769, C_770), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_771, '#skF_2') | ~r1_tarski(C_770, B_771) | ~r1_tarski(A_769, B_771))), inference(resolution, [status(thm)], [c_12, c_193])).
% 12.98/6.29  tff(c_11504, plain, (![A_769, C_770]: (r1_tarski(k5_xboole_0(A_769, C_770), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(C_770, '#skF_2') | ~r1_tarski(A_769, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_11432])).
% 12.98/6.29  tff(c_34, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.98/6.29  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.98/6.29  tff(c_40, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.98/6.29  tff(c_1099, plain, (![B_214, A_215, C_216]: (v2_tops_2(B_214, A_215) | ~v2_tops_2(C_216, A_215) | ~r1_tarski(B_214, C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~m1_subset_1(B_214, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.98/6.29  tff(c_2254, plain, (![A_332, C_333, A_334, B_335]: (v2_tops_2(k5_xboole_0(A_332, C_333), A_334) | ~v2_tops_2(B_335, A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_334)))) | ~m1_subset_1(k5_xboole_0(A_332, C_333), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_334)))) | ~l1_pre_topc(A_334) | ~r1_tarski(C_333, B_335) | ~r1_tarski(A_332, B_335))), inference(resolution, [status(thm)], [c_12, c_1099])).
% 12.98/6.29  tff(c_2261, plain, (![A_332, C_333]: (v2_tops_2(k5_xboole_0(A_332, C_333), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k5_xboole_0(A_332, C_333), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(C_333, '#skF_2') | ~r1_tarski(A_332, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_2254])).
% 12.98/6.29  tff(c_2310, plain, (![A_340, C_341]: (v2_tops_2(k5_xboole_0(A_340, C_341), '#skF_1') | ~m1_subset_1(k5_xboole_0(A_340, C_341), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(C_341, '#skF_2') | ~r1_tarski(A_340, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_2261])).
% 12.98/6.29  tff(c_17039, plain, (![A_927, C_928]: (v2_tops_2(k5_xboole_0(A_927, C_928), '#skF_1') | ~r1_tarski(C_928, '#skF_2') | ~r1_tarski(A_927, '#skF_2') | ~r1_tarski(k5_xboole_0(A_927, C_928), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_34, c_2310])).
% 12.98/6.29  tff(c_17099, plain, (![A_929, C_930]: (v2_tops_2(k5_xboole_0(A_929, C_930), '#skF_1') | ~r1_tarski(C_930, '#skF_2') | ~r1_tarski(A_929, '#skF_2'))), inference(resolution, [status(thm)], [c_11504, c_17039])).
% 12.98/6.29  tff(c_24405, plain, (![A_1080, B_1081]: (v2_tops_2(k4_xboole_0(A_1080, B_1081), '#skF_1') | ~r1_tarski(k3_xboole_0(A_1080, B_1081), '#skF_2') | ~r1_tarski(A_1080, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_17099])).
% 12.98/6.29  tff(c_155, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.98/6.29  tff(c_164, plain, (![C_88]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_44, c_155])).
% 12.98/6.29  tff(c_38, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.98/6.29  tff(c_183, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_38])).
% 12.98/6.29  tff(c_24408, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_24405, c_183])).
% 12.98/6.29  tff(c_24411, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24408])).
% 12.98/6.29  tff(c_24414, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_24411])).
% 12.98/6.29  tff(c_24418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_24414])).
% 12.98/6.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/6.29  
% 12.98/6.29  Inference rules
% 12.98/6.29  ----------------------
% 12.98/6.29  #Ref     : 0
% 12.98/6.29  #Sup     : 6202
% 12.98/6.29  #Fact    : 0
% 12.98/6.29  #Define  : 0
% 12.98/6.29  #Split   : 3
% 12.98/6.29  #Chain   : 0
% 12.98/6.29  #Close   : 0
% 12.98/6.29  
% 12.98/6.29  Ordering : KBO
% 12.98/6.29  
% 12.98/6.29  Simplification rules
% 12.98/6.29  ----------------------
% 12.98/6.29  #Subsume      : 254
% 12.98/6.29  #Demod        : 227
% 12.98/6.29  #Tautology    : 157
% 12.98/6.29  #SimpNegUnit  : 0
% 12.98/6.29  #BackRed      : 1
% 12.98/6.29  
% 12.98/6.29  #Partial instantiations: 0
% 12.98/6.29  #Strategies tried      : 1
% 12.98/6.29  
% 12.98/6.29  Timing (in seconds)
% 12.98/6.29  ----------------------
% 12.98/6.29  Preprocessing        : 0.32
% 12.98/6.29  Parsing              : 0.17
% 12.98/6.29  CNF conversion       : 0.02
% 12.98/6.29  Main loop            : 5.15
% 12.98/6.29  Inferencing          : 0.77
% 12.98/6.29  Reduction            : 1.44
% 12.98/6.29  Demodulation         : 1.16
% 12.98/6.29  BG Simplification    : 0.13
% 12.98/6.29  Subsumption          : 2.47
% 12.98/6.29  Abstraction          : 0.19
% 12.98/6.29  MUC search           : 0.00
% 12.98/6.29  Cooper               : 0.00
% 12.98/6.29  Total                : 5.50
% 12.98/6.29  Index Insertion      : 0.00
% 12.98/6.29  Index Deletion       : 0.00
% 12.98/6.29  Index Matching       : 0.00
% 12.98/6.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
