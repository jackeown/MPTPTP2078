%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 119 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 344 expanded)
%              Number of equality atoms :   23 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_148,plain,(
    ! [B_53,A_54] :
      ( v2_tops_1(B_53,A_54)
      | k1_tops_1(A_54,B_53) != k1_xboole_0
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_155,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_159,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_160,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_159])).

tff(c_123,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_132,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_128])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_265,plain,(
    ! [A_68,B_69] :
      ( v3_pre_topc(k1_tops_1(A_68,B_69),A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_270,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_265])).

tff(c_274,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_270])).

tff(c_59,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_85,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67,c_85])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [C_33] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_33
      | ~ v3_pre_topc(C_33,'#skF_1')
      | ~ r1_tarski(C_33,'#skF_2')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_163,plain,(
    ! [C_55] :
      ( k1_xboole_0 = C_55
      | ~ v3_pre_topc(C_55,'#skF_1')
      | ~ r1_tarski(C_55,'#skF_2')
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_48])).

tff(c_189,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v3_pre_topc(A_58,'#skF_1')
      | ~ r1_tarski(A_58,'#skF_2')
      | ~ r1_tarski(A_58,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_163])).

tff(c_201,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v3_pre_topc(A_43,'#skF_1')
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_88,c_189])).

tff(c_277,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_274,c_201])).

tff(c_280,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_277])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_280])).

tff(c_283,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_284,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_288,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_32])).

tff(c_34,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_286,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_34])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_300,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_36])).

tff(c_509,plain,(
    ! [A_93,B_94] :
      ( k1_tops_1(A_93,B_94) = k1_xboole_0
      | ~ v2_tops_1(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_519,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_509])).

tff(c_526,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_284,c_519])).

tff(c_743,plain,(
    ! [B_107,A_108,C_109] :
      ( r1_tarski(B_107,k1_tops_1(A_108,C_109))
      | ~ r1_tarski(B_107,C_109)
      | ~ v3_pre_topc(B_107,A_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_750,plain,(
    ! [B_107] :
      ( r1_tarski(B_107,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_107,'#skF_2')
      | ~ v3_pre_topc(B_107,'#skF_1')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_743])).

tff(c_819,plain,(
    ! [B_114] :
      ( r1_tarski(B_114,k1_xboole_0)
      | ~ r1_tarski(B_114,'#skF_2')
      | ~ v3_pre_topc(B_114,'#skF_1')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_526,c_750])).

tff(c_822,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_300,c_819])).

tff(c_832,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_286,c_822])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_859,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_832,c_4])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_862,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_6])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.41  
% 3.02/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.41  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.41  
% 3.02/1.41  %Foreground sorts:
% 3.02/1.41  
% 3.02/1.41  
% 3.02/1.41  %Background operators:
% 3.02/1.41  
% 3.02/1.41  
% 3.02/1.41  %Foreground operators:
% 3.02/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.41  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.02/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.02/1.41  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.41  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.41  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.41  
% 3.29/1.43  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.29/1.43  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.29/1.43  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.29/1.43  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.29/1.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.29/1.43  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.29/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/1.43  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.29/1.43  tff(c_30, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_56, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.29/1.43  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_148, plain, (![B_53, A_54]: (v2_tops_1(B_53, A_54) | k1_tops_1(A_54, B_53)!=k1_xboole_0 | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.43  tff(c_155, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_148])).
% 3.29/1.43  tff(c_159, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_155])).
% 3.29/1.43  tff(c_160, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_159])).
% 3.29/1.43  tff(c_123, plain, (![A_50, B_51]: (r1_tarski(k1_tops_1(A_50, B_51), B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.43  tff(c_128, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_123])).
% 3.29/1.43  tff(c_132, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_128])).
% 3.29/1.43  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_265, plain, (![A_68, B_69]: (v3_pre_topc(k1_tops_1(A_68, B_69), A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.43  tff(c_270, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_265])).
% 3.29/1.43  tff(c_274, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_270])).
% 3.29/1.43  tff(c_59, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.43  tff(c_67, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_59])).
% 3.29/1.43  tff(c_85, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.43  tff(c_88, plain, (![A_43]: (r1_tarski(A_43, u1_struct_0('#skF_1')) | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_67, c_85])).
% 3.29/1.43  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.43  tff(c_48, plain, (![C_33]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_33 | ~v3_pre_topc(C_33, '#skF_1') | ~r1_tarski(C_33, '#skF_2') | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_163, plain, (![C_55]: (k1_xboole_0=C_55 | ~v3_pre_topc(C_55, '#skF_1') | ~r1_tarski(C_55, '#skF_2') | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_48])).
% 3.29/1.43  tff(c_189, plain, (![A_58]: (k1_xboole_0=A_58 | ~v3_pre_topc(A_58, '#skF_1') | ~r1_tarski(A_58, '#skF_2') | ~r1_tarski(A_58, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_163])).
% 3.29/1.43  tff(c_201, plain, (![A_43]: (k1_xboole_0=A_43 | ~v3_pre_topc(A_43, '#skF_1') | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_189])).
% 3.29/1.43  tff(c_277, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_274, c_201])).
% 3.29/1.43  tff(c_280, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_277])).
% 3.29/1.43  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_280])).
% 3.29/1.43  tff(c_283, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.29/1.43  tff(c_284, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.29/1.43  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_288, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_32])).
% 3.29/1.43  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_286, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_34])).
% 3.29/1.43  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.43  tff(c_300, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_36])).
% 3.29/1.43  tff(c_509, plain, (![A_93, B_94]: (k1_tops_1(A_93, B_94)=k1_xboole_0 | ~v2_tops_1(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.43  tff(c_519, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_509])).
% 3.29/1.43  tff(c_526, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_284, c_519])).
% 3.29/1.43  tff(c_743, plain, (![B_107, A_108, C_109]: (r1_tarski(B_107, k1_tops_1(A_108, C_109)) | ~r1_tarski(B_107, C_109) | ~v3_pre_topc(B_107, A_108) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.29/1.43  tff(c_750, plain, (![B_107]: (r1_tarski(B_107, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_107, '#skF_2') | ~v3_pre_topc(B_107, '#skF_1') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_743])).
% 3.29/1.43  tff(c_819, plain, (![B_114]: (r1_tarski(B_114, k1_xboole_0) | ~r1_tarski(B_114, '#skF_2') | ~v3_pre_topc(B_114, '#skF_1') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_526, c_750])).
% 3.29/1.43  tff(c_822, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_300, c_819])).
% 3.29/1.43  tff(c_832, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_288, c_286, c_822])).
% 3.29/1.43  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.43  tff(c_859, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_832, c_4])).
% 3.29/1.43  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.43  tff(c_862, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_859, c_6])).
% 3.29/1.43  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_862])).
% 3.29/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.43  
% 3.29/1.43  Inference rules
% 3.29/1.43  ----------------------
% 3.29/1.43  #Ref     : 0
% 3.29/1.43  #Sup     : 190
% 3.29/1.43  #Fact    : 0
% 3.29/1.43  #Define  : 0
% 3.29/1.43  #Split   : 8
% 3.29/1.43  #Chain   : 0
% 3.29/1.43  #Close   : 0
% 3.29/1.43  
% 3.29/1.43  Ordering : KBO
% 3.29/1.43  
% 3.29/1.43  Simplification rules
% 3.29/1.43  ----------------------
% 3.29/1.43  #Subsume      : 35
% 3.29/1.43  #Demod        : 75
% 3.29/1.43  #Tautology    : 78
% 3.29/1.43  #SimpNegUnit  : 9
% 3.29/1.43  #BackRed      : 3
% 3.29/1.43  
% 3.29/1.43  #Partial instantiations: 0
% 3.29/1.43  #Strategies tried      : 1
% 3.29/1.43  
% 3.29/1.43  Timing (in seconds)
% 3.29/1.43  ----------------------
% 3.29/1.43  Preprocessing        : 0.31
% 3.29/1.43  Parsing              : 0.17
% 3.29/1.43  CNF conversion       : 0.02
% 3.29/1.43  Main loop            : 0.36
% 3.29/1.43  Inferencing          : 0.13
% 3.29/1.43  Reduction            : 0.11
% 3.29/1.43  Demodulation         : 0.07
% 3.29/1.43  BG Simplification    : 0.02
% 3.29/1.43  Subsumption          : 0.08
% 3.29/1.43  Abstraction          : 0.01
% 3.29/1.43  MUC search           : 0.00
% 3.29/1.43  Cooper               : 0.00
% 3.29/1.43  Total                : 0.70
% 3.29/1.43  Index Insertion      : 0.00
% 3.29/1.43  Index Deletion       : 0.00
% 3.29/1.43  Index Matching       : 0.00
% 3.29/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
