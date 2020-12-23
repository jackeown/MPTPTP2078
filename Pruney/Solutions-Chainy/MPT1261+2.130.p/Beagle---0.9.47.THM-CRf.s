%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 273 expanded)
%              Number of equality atoms :   43 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_823,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_subset_1(A_108,B_109,C_110) = k4_xboole_0(B_109,C_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_829,plain,(
    ! [C_110] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_26,c_823])).

tff(c_32,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_225,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_569,plain,(
    ! [B_78,A_79] :
      ( v4_pre_topc(B_78,A_79)
      | k2_pre_topc(A_79,B_78) != B_78
      | ~ v2_pre_topc(A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_576,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_569])).

tff(c_580,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_576])).

tff(c_581,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_580])).

tff(c_115,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_115])).

tff(c_230,plain,(
    ! [A_51,B_52,C_53] :
      ( k7_subset_1(A_51,B_52,C_53) = k4_xboole_0(B_52,C_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_237,plain,(
    ! [C_54] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_54) = k4_xboole_0('#skF_2',C_54) ),
    inference(resolution,[status(thm)],[c_26,c_230])).

tff(c_38,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_111,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_243,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_111])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_36,B_37] : k2_xboole_0(k4_xboole_0(A_36,B_37),A_36) = A_36 ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_264,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_85])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_261,plain,(
    ! [B_4] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_4)
      | ~ r1_tarski('#skF_2',B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_4])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_464,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_535,plain,(
    ! [B_74,B_75,A_76] :
      ( k4_subset_1(B_74,B_75,A_76) = k2_xboole_0(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(B_74))
      | ~ r1_tarski(A_76,B_74) ) ),
    inference(resolution,[status(thm)],[c_16,c_464])).

tff(c_542,plain,(
    ! [A_77] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_77) = k2_xboole_0('#skF_2',A_77)
      | ~ r1_tarski(A_77,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_535])).

tff(c_546,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_261,c_542])).

tff(c_560,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_264,c_546])).

tff(c_691,plain,(
    ! [A_95,B_96] :
      ( k4_subset_1(u1_struct_0(A_95),B_96,k2_tops_1(A_95,B_96)) = k2_pre_topc(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_696,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_691])).

tff(c_700,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_560,c_696])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_700])).

tff(c_703,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_111])).

tff(c_706,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_729,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_32])).

tff(c_830,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_729])).

tff(c_860,plain,(
    ! [A_118,B_119] :
      ( k2_pre_topc(A_118,B_119) = B_119
      | ~ v4_pre_topc(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_867,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_860])).

tff(c_871,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_706,c_867])).

tff(c_1148,plain,(
    ! [A_162,B_163] :
      ( k7_subset_1(u1_struct_0(A_162),k2_pre_topc(A_162,B_163),k1_tops_1(A_162,B_163)) = k2_tops_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1157,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_1148])).

tff(c_1161,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_829,c_1157])).

tff(c_1163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_1161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.07/1.48  
% 3.07/1.48  %Foreground sorts:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Background operators:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Foreground operators:
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.07/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.07/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.07/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.07/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.07/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.07/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.48  
% 3.21/1.49  tff(f_92, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.21/1.49  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.21/1.49  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.21/1.49  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.49  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.21/1.49  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.21/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.21/1.49  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.21/1.49  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.21/1.49  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.21/1.49  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.21/1.49  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.49  tff(c_823, plain, (![A_108, B_109, C_110]: (k7_subset_1(A_108, B_109, C_110)=k4_xboole_0(B_109, C_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.49  tff(c_829, plain, (![C_110]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_26, c_823])).
% 3.21/1.49  tff(c_32, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.49  tff(c_225, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.21/1.49  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.49  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.49  tff(c_569, plain, (![B_78, A_79]: (v4_pre_topc(B_78, A_79) | k2_pre_topc(A_79, B_78)!=B_78 | ~v2_pre_topc(A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.49  tff(c_576, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_569])).
% 3.21/1.49  tff(c_580, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_576])).
% 3.21/1.49  tff(c_581, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_225, c_580])).
% 3.21/1.49  tff(c_115, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_123, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_115])).
% 3.21/1.49  tff(c_230, plain, (![A_51, B_52, C_53]: (k7_subset_1(A_51, B_52, C_53)=k4_xboole_0(B_52, C_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.49  tff(c_237, plain, (![C_54]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_54)=k4_xboole_0('#skF_2', C_54))), inference(resolution, [status(thm)], [c_26, c_230])).
% 3.21/1.49  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.49  tff(c_111, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 3.21/1.49  tff(c_243, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_237, c_111])).
% 3.21/1.49  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.49  tff(c_74, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.49  tff(c_79, plain, (![A_36, B_37]: (k2_xboole_0(k4_xboole_0(A_36, B_37), A_36)=A_36)), inference(resolution, [status(thm)], [c_8, c_74])).
% 3.21/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.49  tff(c_85, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k4_xboole_0(A_36, B_37))=A_36)), inference(superposition, [status(thm), theory('equality')], [c_79, c_2])).
% 3.21/1.49  tff(c_264, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_243, c_85])).
% 3.21/1.49  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.49  tff(c_261, plain, (![B_4]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_4) | ~r1_tarski('#skF_2', B_4))), inference(superposition, [status(thm), theory('equality')], [c_243, c_4])).
% 3.21/1.49  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_464, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.49  tff(c_535, plain, (![B_74, B_75, A_76]: (k4_subset_1(B_74, B_75, A_76)=k2_xboole_0(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(B_74)) | ~r1_tarski(A_76, B_74))), inference(resolution, [status(thm)], [c_16, c_464])).
% 3.21/1.49  tff(c_542, plain, (![A_77]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_77)=k2_xboole_0('#skF_2', A_77) | ~r1_tarski(A_77, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_535])).
% 3.21/1.49  tff(c_546, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_261, c_542])).
% 3.21/1.49  tff(c_560, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_264, c_546])).
% 3.21/1.49  tff(c_691, plain, (![A_95, B_96]: (k4_subset_1(u1_struct_0(A_95), B_96, k2_tops_1(A_95, B_96))=k2_pre_topc(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.49  tff(c_696, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_691])).
% 3.21/1.49  tff(c_700, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_560, c_696])).
% 3.21/1.49  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_700])).
% 3.21/1.49  tff(c_703, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 3.21/1.49  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_703, c_111])).
% 3.21/1.49  tff(c_706, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 3.21/1.49  tff(c_729, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_32])).
% 3.21/1.49  tff(c_830, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_829, c_729])).
% 3.21/1.49  tff(c_860, plain, (![A_118, B_119]: (k2_pre_topc(A_118, B_119)=B_119 | ~v4_pre_topc(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.49  tff(c_867, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_860])).
% 3.21/1.49  tff(c_871, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_706, c_867])).
% 3.21/1.49  tff(c_1148, plain, (![A_162, B_163]: (k7_subset_1(u1_struct_0(A_162), k2_pre_topc(A_162, B_163), k1_tops_1(A_162, B_163))=k2_tops_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.21/1.49  tff(c_1157, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_871, c_1148])).
% 3.21/1.49  tff(c_1161, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_829, c_1157])).
% 3.21/1.49  tff(c_1163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_1161])).
% 3.21/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  Inference rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Ref     : 0
% 3.21/1.49  #Sup     : 264
% 3.21/1.49  #Fact    : 0
% 3.21/1.49  #Define  : 0
% 3.21/1.49  #Split   : 2
% 3.21/1.49  #Chain   : 0
% 3.21/1.49  #Close   : 0
% 3.21/1.49  
% 3.21/1.49  Ordering : KBO
% 3.21/1.49  
% 3.21/1.49  Simplification rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Subsume      : 40
% 3.21/1.49  #Demod        : 69
% 3.21/1.49  #Tautology    : 140
% 3.21/1.49  #SimpNegUnit  : 4
% 3.21/1.49  #BackRed      : 1
% 3.21/1.49  
% 3.21/1.49  #Partial instantiations: 0
% 3.21/1.49  #Strategies tried      : 1
% 3.21/1.49  
% 3.21/1.49  Timing (in seconds)
% 3.21/1.49  ----------------------
% 3.21/1.50  Preprocessing        : 0.32
% 3.21/1.50  Parsing              : 0.17
% 3.21/1.50  CNF conversion       : 0.02
% 3.21/1.50  Main loop            : 0.41
% 3.21/1.50  Inferencing          : 0.16
% 3.21/1.50  Reduction            : 0.13
% 3.21/1.50  Demodulation         : 0.10
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.07
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.76
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
