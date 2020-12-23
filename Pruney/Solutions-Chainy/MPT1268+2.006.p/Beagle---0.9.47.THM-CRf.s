%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 131 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 358 expanded)
%              Number of equality atoms :   31 (  62 expanded)
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

tff(f_102,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_45,axiom,(
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

tff(f_74,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_372,plain,(
    ! [B_66,A_67] :
      ( v2_tops_1(B_66,A_67)
      | k1_tops_1(A_67,B_66) != k1_xboole_0
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_379,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_383,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_379])).

tff(c_384,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_383])).

tff(c_249,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tops_1(A_58,B_59),B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_254,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_258,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_254])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_289,plain,(
    ! [A_62,B_63] :
      ( v3_pre_topc(k1_tops_1(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_294,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_298,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_294])).

tff(c_102,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_120,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_47,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_110,c_120])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [C_35] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_269,plain,(
    ! [C_60] :
      ( k1_xboole_0 = C_60
      | ~ v3_pre_topc(C_60,'#skF_1')
      | ~ r1_tarski(C_60,'#skF_2')
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50])).

tff(c_649,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ v3_pre_topc(A_90,'#skF_1')
      | ~ r1_tarski(A_90,'#skF_2')
      | ~ r1_tarski(A_90,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_269])).

tff(c_676,plain,(
    ! [A_91] :
      ( k1_xboole_0 = A_91
      | ~ v3_pre_topc(A_91,'#skF_1')
      | ~ r1_tarski(A_91,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_125,c_649])).

tff(c_679,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_676])).

tff(c_682,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_679])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_682])).

tff(c_685,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_686,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_723,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_34])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_688,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_36])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_741,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_38])).

tff(c_963,plain,(
    ! [A_117,B_118] :
      ( k1_tops_1(A_117,B_118) = k1_xboole_0
      | ~ v2_tops_1(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_973,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_963])).

tff(c_980,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_686,c_973])).

tff(c_1336,plain,(
    ! [B_130,A_131,C_132] :
      ( r1_tarski(B_130,k1_tops_1(A_131,C_132))
      | ~ r1_tarski(B_130,C_132)
      | ~ v3_pre_topc(B_130,A_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1343,plain,(
    ! [B_130] :
      ( r1_tarski(B_130,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_130,'#skF_2')
      | ~ v3_pre_topc(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1336])).

tff(c_1352,plain,(
    ! [B_133] :
      ( r1_tarski(B_133,k1_xboole_0)
      | ~ r1_tarski(B_133,'#skF_2')
      | ~ v3_pre_topc(B_133,'#skF_1')
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_980,c_1343])).

tff(c_1355,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_741,c_1352])).

tff(c_1365,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_688,c_1355])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1377,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1365,c_4])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_724,plain,(
    ! [A_94,B_95] : k1_setfam_1(k2_tarski(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_818,plain,(
    ! [A_109,B_110] : k1_setfam_1(k2_tarski(A_109,B_110)) = k3_xboole_0(B_110,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_724])).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_841,plain,(
    ! [B_111,A_112] : k3_xboole_0(B_111,A_112) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_10])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_742,plain,(
    ! [A_98,B_99] :
      ( k3_xboole_0(A_98,B_99) = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_750,plain,(
    ! [A_6] : k3_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_857,plain,(
    ! [B_111] : k3_xboole_0(B_111,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_750])).

tff(c_1408,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_857])).

tff(c_1414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.50  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.13/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.13/1.50  
% 3.32/1.51  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.32/1.51  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.32/1.51  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.51  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.51  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.32/1.51  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.32/1.51  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.51  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.32/1.51  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.32/1.51  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.51  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_52, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.32/1.51  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_372, plain, (![B_66, A_67]: (v2_tops_1(B_66, A_67) | k1_tops_1(A_67, B_66)!=k1_xboole_0 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.51  tff(c_379, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_372])).
% 3.32/1.51  tff(c_383, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_379])).
% 3.32/1.51  tff(c_384, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_383])).
% 3.32/1.51  tff(c_249, plain, (![A_58, B_59]: (r1_tarski(k1_tops_1(A_58, B_59), B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.51  tff(c_254, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_249])).
% 3.32/1.51  tff(c_258, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_254])).
% 3.32/1.51  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_289, plain, (![A_62, B_63]: (v3_pre_topc(k1_tops_1(A_62, B_63), A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.51  tff(c_294, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_289])).
% 3.32/1.51  tff(c_298, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_294])).
% 3.32/1.51  tff(c_102, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.51  tff(c_110, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_102])).
% 3.32/1.51  tff(c_120, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.51  tff(c_125, plain, (![A_47]: (r1_tarski(A_47, u1_struct_0('#skF_1')) | ~r1_tarski(A_47, '#skF_2'))), inference(resolution, [status(thm)], [c_110, c_120])).
% 3.32/1.51  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.51  tff(c_50, plain, (![C_35]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_269, plain, (![C_60]: (k1_xboole_0=C_60 | ~v3_pre_topc(C_60, '#skF_1') | ~r1_tarski(C_60, '#skF_2') | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_50])).
% 3.32/1.51  tff(c_649, plain, (![A_90]: (k1_xboole_0=A_90 | ~v3_pre_topc(A_90, '#skF_1') | ~r1_tarski(A_90, '#skF_2') | ~r1_tarski(A_90, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_269])).
% 3.32/1.51  tff(c_676, plain, (![A_91]: (k1_xboole_0=A_91 | ~v3_pre_topc(A_91, '#skF_1') | ~r1_tarski(A_91, '#skF_2'))), inference(resolution, [status(thm)], [c_125, c_649])).
% 3.32/1.51  tff(c_679, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_298, c_676])).
% 3.32/1.51  tff(c_682, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_258, c_679])).
% 3.32/1.51  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_384, c_682])).
% 3.32/1.51  tff(c_685, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.32/1.51  tff(c_686, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.32/1.51  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_723, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_34])).
% 3.32/1.51  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_688, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_36])).
% 3.32/1.51  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.51  tff(c_741, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_38])).
% 3.32/1.51  tff(c_963, plain, (![A_117, B_118]: (k1_tops_1(A_117, B_118)=k1_xboole_0 | ~v2_tops_1(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.51  tff(c_973, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_963])).
% 3.32/1.51  tff(c_980, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_686, c_973])).
% 3.32/1.51  tff(c_1336, plain, (![B_130, A_131, C_132]: (r1_tarski(B_130, k1_tops_1(A_131, C_132)) | ~r1_tarski(B_130, C_132) | ~v3_pre_topc(B_130, A_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.32/1.51  tff(c_1343, plain, (![B_130]: (r1_tarski(B_130, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_130, '#skF_2') | ~v3_pre_topc(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1336])).
% 3.32/1.51  tff(c_1352, plain, (![B_133]: (r1_tarski(B_133, k1_xboole_0) | ~r1_tarski(B_133, '#skF_2') | ~v3_pre_topc(B_133, '#skF_1') | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_980, c_1343])).
% 3.32/1.51  tff(c_1355, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_741, c_1352])).
% 3.32/1.51  tff(c_1365, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_723, c_688, c_1355])).
% 3.32/1.51  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.51  tff(c_1377, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_1365, c_4])).
% 3.32/1.51  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.51  tff(c_724, plain, (![A_94, B_95]: (k1_setfam_1(k2_tarski(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.51  tff(c_818, plain, (![A_109, B_110]: (k1_setfam_1(k2_tarski(A_109, B_110))=k3_xboole_0(B_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_8, c_724])).
% 3.32/1.51  tff(c_10, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.51  tff(c_841, plain, (![B_111, A_112]: (k3_xboole_0(B_111, A_112)=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_818, c_10])).
% 3.32/1.51  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.51  tff(c_742, plain, (![A_98, B_99]: (k3_xboole_0(A_98, B_99)=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.51  tff(c_750, plain, (![A_6]: (k3_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_742])).
% 3.32/1.51  tff(c_857, plain, (![B_111]: (k3_xboole_0(B_111, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_841, c_750])).
% 3.32/1.51  tff(c_1408, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1377, c_857])).
% 3.32/1.51  tff(c_1414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1408])).
% 3.32/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.51  
% 3.32/1.51  Inference rules
% 3.32/1.51  ----------------------
% 3.32/1.51  #Ref     : 0
% 3.32/1.51  #Sup     : 319
% 3.32/1.51  #Fact    : 0
% 3.32/1.51  #Define  : 0
% 3.32/1.51  #Split   : 4
% 3.32/1.51  #Chain   : 0
% 3.32/1.51  #Close   : 0
% 3.32/1.51  
% 3.32/1.51  Ordering : KBO
% 3.32/1.51  
% 3.32/1.51  Simplification rules
% 3.32/1.51  ----------------------
% 3.32/1.51  #Subsume      : 55
% 3.32/1.51  #Demod        : 110
% 3.32/1.51  #Tautology    : 187
% 3.32/1.51  #SimpNegUnit  : 6
% 3.32/1.51  #BackRed      : 1
% 3.32/1.51  
% 3.32/1.51  #Partial instantiations: 0
% 3.32/1.51  #Strategies tried      : 1
% 3.32/1.51  
% 3.32/1.51  Timing (in seconds)
% 3.32/1.51  ----------------------
% 3.32/1.51  Preprocessing        : 0.32
% 3.32/1.51  Parsing              : 0.17
% 3.32/1.52  CNF conversion       : 0.02
% 3.32/1.52  Main loop            : 0.43
% 3.32/1.52  Inferencing          : 0.15
% 3.32/1.52  Reduction            : 0.14
% 3.32/1.52  Demodulation         : 0.10
% 3.32/1.52  BG Simplification    : 0.02
% 3.32/1.52  Subsumption          : 0.08
% 3.32/1.52  Abstraction          : 0.02
% 3.32/1.52  MUC search           : 0.00
% 3.32/1.52  Cooper               : 0.00
% 3.32/1.52  Total                : 0.78
% 3.32/1.52  Index Insertion      : 0.00
% 3.32/1.52  Index Deletion       : 0.00
% 3.32/1.52  Index Matching       : 0.00
% 3.32/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
