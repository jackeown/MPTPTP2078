%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 10.79s
% Output     : CNFRefutation 10.79s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 228 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_92,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_92])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_343,plain,(
    ! [C_69,A_70,B_71] :
      ( v2_tex_2(C_69,A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ r1_tarski(C_69,B_71)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_876,plain,(
    ! [A_113,B_114,A_115] :
      ( v2_tex_2(k3_xboole_0(A_113,B_114),A_115)
      | ~ v2_tex_2(A_113,A_115)
      | ~ m1_subset_1(k3_xboole_0(A_113,B_114),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(A_113,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_4,c_343])).

tff(c_3418,plain,(
    ! [A_176,B_177,A_178] :
      ( v2_tex_2(k3_xboole_0(A_176,B_177),A_178)
      | ~ v2_tex_2(A_176,A_178)
      | ~ m1_subset_1(A_176,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178)
      | ~ r1_tarski(k3_xboole_0(A_176,B_177),u1_struct_0(A_178)) ) ),
    inference(resolution,[status(thm)],[c_14,c_876])).

tff(c_3494,plain,(
    ! [A_176,B_177] :
      ( v2_tex_2(k3_xboole_0(A_176,B_177),'#skF_1')
      | ~ v2_tex_2(A_176,'#skF_1')
      | ~ m1_subset_1(A_176,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_176,B_177),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_102,c_3418])).

tff(c_10640,plain,(
    ! [A_343,B_344] :
      ( v2_tex_2(k3_xboole_0(A_343,B_344),'#skF_1')
      | ~ v2_tex_2(A_343,'#skF_1')
      | ~ m1_subset_1(A_343,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_343,B_344),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3494])).

tff(c_10647,plain,(
    ! [B_344] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_344),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_344),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_10640])).

tff(c_10656,plain,(
    ! [B_345] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_345),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_345),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10647])).

tff(c_10673,plain,(
    ! [B_346] :
      ( v2_tex_2(k3_xboole_0(B_346,'#skF_2'),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_346),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10656])).

tff(c_105,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_18,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_140,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_141,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_10676,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10673,c_141])).

tff(c_10700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_10676])).

tff(c_10701,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_10714,plain,(
    ! [A_351,B_352] :
      ( r1_tarski(A_351,B_352)
      | ~ m1_subset_1(A_351,k1_zfmisc_1(B_352)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10725,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_10714])).

tff(c_10727,plain,(
    ! [A_353,C_354,B_355] :
      ( r1_tarski(A_353,C_354)
      | ~ r1_tarski(B_355,C_354)
      | ~ r1_tarski(A_353,B_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10737,plain,(
    ! [A_353] :
      ( r1_tarski(A_353,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_353,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10725,c_10727])).

tff(c_11080,plain,(
    ! [C_394,A_395,B_396] :
      ( v2_tex_2(C_394,A_395)
      | ~ v2_tex_2(B_396,A_395)
      | ~ r1_tarski(C_394,B_396)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11614,plain,(
    ! [A_435,B_436,A_437] :
      ( v2_tex_2(k3_xboole_0(A_435,B_436),A_437)
      | ~ v2_tex_2(A_435,A_437)
      | ~ m1_subset_1(k3_xboole_0(A_435,B_436),k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_subset_1(A_435,k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ l1_pre_topc(A_437) ) ),
    inference(resolution,[status(thm)],[c_4,c_11080])).

tff(c_14043,plain,(
    ! [A_492,B_493,A_494] :
      ( v2_tex_2(k3_xboole_0(A_492,B_493),A_494)
      | ~ v2_tex_2(A_492,A_494)
      | ~ m1_subset_1(A_492,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ l1_pre_topc(A_494)
      | ~ r1_tarski(k3_xboole_0(A_492,B_493),u1_struct_0(A_494)) ) ),
    inference(resolution,[status(thm)],[c_14,c_11614])).

tff(c_14119,plain,(
    ! [A_492,B_493] :
      ( v2_tex_2(k3_xboole_0(A_492,B_493),'#skF_1')
      | ~ v2_tex_2(A_492,'#skF_1')
      | ~ m1_subset_1(A_492,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_492,B_493),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10737,c_14043])).

tff(c_20438,plain,(
    ! [A_646,B_647] :
      ( v2_tex_2(k3_xboole_0(A_646,B_647),'#skF_1')
      | ~ v2_tex_2(A_646,'#skF_1')
      | ~ m1_subset_1(A_646,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_646,B_647),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14119])).

tff(c_20443,plain,(
    ! [B_647] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_647),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_647),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_20438])).

tff(c_20449,plain,(
    ! [B_647] : v2_tex_2(k3_xboole_0('#skF_3',B_647),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10701,c_20443])).

tff(c_10813,plain,(
    ! [A_367,B_368,C_369] :
      ( k9_subset_1(A_367,B_368,C_369) = k3_xboole_0(B_368,C_369)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(A_367)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10821,plain,(
    ! [B_368] : k9_subset_1(u1_struct_0('#skF_1'),B_368,'#skF_3') = k3_xboole_0(B_368,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_10813])).

tff(c_10901,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10821,c_18])).

tff(c_10902,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10901])).

tff(c_20453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20449,c_10902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.79/4.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.79/4.27  
% 10.79/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.79/4.27  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.79/4.27  
% 10.79/4.27  %Foreground sorts:
% 10.79/4.27  
% 10.79/4.27  
% 10.79/4.27  %Background operators:
% 10.79/4.27  
% 10.79/4.27  
% 10.79/4.27  %Foreground operators:
% 10.79/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.79/4.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.79/4.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.79/4.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.79/4.27  tff('#skF_2', type, '#skF_2': $i).
% 10.79/4.27  tff('#skF_3', type, '#skF_3': $i).
% 10.79/4.27  tff('#skF_1', type, '#skF_1': $i).
% 10.79/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.79/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.79/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.79/4.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.79/4.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.79/4.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.79/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.79/4.27  
% 10.79/4.28  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.79/4.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.79/4.28  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 10.79/4.28  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.79/4.28  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.79/4.28  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 10.79/4.28  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.79/4.28  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.79/4.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.79/4.28  tff(c_20, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.79/4.28  tff(c_67, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 10.79/4.28  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.79/4.28  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.79/4.28  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.79/4.28  tff(c_79, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.79/4.28  tff(c_90, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_79])).
% 10.79/4.28  tff(c_92, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.79/4.28  tff(c_102, plain, (![A_37]: (r1_tarski(A_37, u1_struct_0('#skF_1')) | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_92])).
% 10.79/4.28  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.79/4.28  tff(c_343, plain, (![C_69, A_70, B_71]: (v2_tex_2(C_69, A_70) | ~v2_tex_2(B_71, A_70) | ~r1_tarski(C_69, B_71) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.79/4.28  tff(c_876, plain, (![A_113, B_114, A_115]: (v2_tex_2(k3_xboole_0(A_113, B_114), A_115) | ~v2_tex_2(A_113, A_115) | ~m1_subset_1(k3_xboole_0(A_113, B_114), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(A_113, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_4, c_343])).
% 10.79/4.28  tff(c_3418, plain, (![A_176, B_177, A_178]: (v2_tex_2(k3_xboole_0(A_176, B_177), A_178) | ~v2_tex_2(A_176, A_178) | ~m1_subset_1(A_176, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178) | ~r1_tarski(k3_xboole_0(A_176, B_177), u1_struct_0(A_178)))), inference(resolution, [status(thm)], [c_14, c_876])).
% 10.79/4.28  tff(c_3494, plain, (![A_176, B_177]: (v2_tex_2(k3_xboole_0(A_176, B_177), '#skF_1') | ~v2_tex_2(A_176, '#skF_1') | ~m1_subset_1(A_176, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_176, B_177), '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_3418])).
% 10.79/4.28  tff(c_10640, plain, (![A_343, B_344]: (v2_tex_2(k3_xboole_0(A_343, B_344), '#skF_1') | ~v2_tex_2(A_343, '#skF_1') | ~m1_subset_1(A_343, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_343, B_344), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3494])).
% 10.79/4.28  tff(c_10647, plain, (![B_344]: (v2_tex_2(k3_xboole_0('#skF_2', B_344), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_344), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_10640])).
% 10.79/4.28  tff(c_10656, plain, (![B_345]: (v2_tex_2(k3_xboole_0('#skF_2', B_345), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_345), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10647])).
% 10.79/4.28  tff(c_10673, plain, (![B_346]: (v2_tex_2(k3_xboole_0(B_346, '#skF_2'), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_346), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10656])).
% 10.79/4.28  tff(c_105, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.79/4.28  tff(c_113, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_105])).
% 10.79/4.28  tff(c_18, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.79/4.28  tff(c_140, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_18])).
% 10.79/4.28  tff(c_141, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_140])).
% 10.79/4.28  tff(c_10676, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_10673, c_141])).
% 10.79/4.28  tff(c_10700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_10676])).
% 10.79/4.28  tff(c_10701, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 10.79/4.28  tff(c_10714, plain, (![A_351, B_352]: (r1_tarski(A_351, B_352) | ~m1_subset_1(A_351, k1_zfmisc_1(B_352)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.79/4.28  tff(c_10725, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_10714])).
% 10.79/4.28  tff(c_10727, plain, (![A_353, C_354, B_355]: (r1_tarski(A_353, C_354) | ~r1_tarski(B_355, C_354) | ~r1_tarski(A_353, B_355))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.79/4.28  tff(c_10737, plain, (![A_353]: (r1_tarski(A_353, u1_struct_0('#skF_1')) | ~r1_tarski(A_353, '#skF_3'))), inference(resolution, [status(thm)], [c_10725, c_10727])).
% 10.79/4.28  tff(c_11080, plain, (![C_394, A_395, B_396]: (v2_tex_2(C_394, A_395) | ~v2_tex_2(B_396, A_395) | ~r1_tarski(C_394, B_396) | ~m1_subset_1(C_394, k1_zfmisc_1(u1_struct_0(A_395))) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.79/4.28  tff(c_11614, plain, (![A_435, B_436, A_437]: (v2_tex_2(k3_xboole_0(A_435, B_436), A_437) | ~v2_tex_2(A_435, A_437) | ~m1_subset_1(k3_xboole_0(A_435, B_436), k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_subset_1(A_435, k1_zfmisc_1(u1_struct_0(A_437))) | ~l1_pre_topc(A_437))), inference(resolution, [status(thm)], [c_4, c_11080])).
% 10.79/4.28  tff(c_14043, plain, (![A_492, B_493, A_494]: (v2_tex_2(k3_xboole_0(A_492, B_493), A_494) | ~v2_tex_2(A_492, A_494) | ~m1_subset_1(A_492, k1_zfmisc_1(u1_struct_0(A_494))) | ~l1_pre_topc(A_494) | ~r1_tarski(k3_xboole_0(A_492, B_493), u1_struct_0(A_494)))), inference(resolution, [status(thm)], [c_14, c_11614])).
% 10.79/4.28  tff(c_14119, plain, (![A_492, B_493]: (v2_tex_2(k3_xboole_0(A_492, B_493), '#skF_1') | ~v2_tex_2(A_492, '#skF_1') | ~m1_subset_1(A_492, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_492, B_493), '#skF_3'))), inference(resolution, [status(thm)], [c_10737, c_14043])).
% 10.79/4.28  tff(c_20438, plain, (![A_646, B_647]: (v2_tex_2(k3_xboole_0(A_646, B_647), '#skF_1') | ~v2_tex_2(A_646, '#skF_1') | ~m1_subset_1(A_646, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_646, B_647), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14119])).
% 10.79/4.28  tff(c_20443, plain, (![B_647]: (v2_tex_2(k3_xboole_0('#skF_3', B_647), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', B_647), '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_20438])).
% 10.79/4.28  tff(c_20449, plain, (![B_647]: (v2_tex_2(k3_xboole_0('#skF_3', B_647), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10701, c_20443])).
% 10.79/4.28  tff(c_10813, plain, (![A_367, B_368, C_369]: (k9_subset_1(A_367, B_368, C_369)=k3_xboole_0(B_368, C_369) | ~m1_subset_1(C_369, k1_zfmisc_1(A_367)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.79/4.28  tff(c_10821, plain, (![B_368]: (k9_subset_1(u1_struct_0('#skF_1'), B_368, '#skF_3')=k3_xboole_0(B_368, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_10813])).
% 10.79/4.28  tff(c_10901, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10821, c_18])).
% 10.79/4.28  tff(c_10902, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10901])).
% 10.79/4.28  tff(c_20453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20449, c_10902])).
% 10.79/4.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.79/4.28  
% 10.79/4.28  Inference rules
% 10.79/4.28  ----------------------
% 10.79/4.28  #Ref     : 0
% 10.79/4.28  #Sup     : 5044
% 10.79/4.28  #Fact    : 0
% 10.79/4.28  #Define  : 0
% 10.79/4.28  #Split   : 2
% 10.79/4.28  #Chain   : 0
% 10.79/4.28  #Close   : 0
% 10.79/4.28  
% 10.79/4.28  Ordering : KBO
% 10.79/4.28  
% 10.79/4.28  Simplification rules
% 10.79/4.28  ----------------------
% 10.79/4.28  #Subsume      : 679
% 10.79/4.28  #Demod        : 1872
% 10.79/4.28  #Tautology    : 1983
% 10.79/4.28  #SimpNegUnit  : 0
% 10.79/4.28  #BackRed      : 3
% 10.79/4.28  
% 10.79/4.28  #Partial instantiations: 0
% 10.79/4.28  #Strategies tried      : 1
% 10.79/4.28  
% 10.79/4.28  Timing (in seconds)
% 10.79/4.28  ----------------------
% 10.79/4.28  Preprocessing        : 0.30
% 10.79/4.28  Parsing              : 0.16
% 10.79/4.28  CNF conversion       : 0.02
% 10.79/4.28  Main loop            : 3.23
% 10.79/4.28  Inferencing          : 0.71
% 10.79/4.28  Reduction            : 1.75
% 10.79/4.28  Demodulation         : 1.59
% 10.79/4.28  BG Simplification    : 0.09
% 10.79/4.29  Subsumption          : 0.49
% 10.79/4.29  Abstraction          : 0.13
% 10.79/4.29  MUC search           : 0.00
% 10.79/4.29  Cooper               : 0.00
% 10.79/4.29  Total                : 3.55
% 10.79/4.29  Index Insertion      : 0.00
% 10.79/4.29  Index Deletion       : 0.00
% 10.79/4.29  Index Matching       : 0.00
% 10.79/4.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
