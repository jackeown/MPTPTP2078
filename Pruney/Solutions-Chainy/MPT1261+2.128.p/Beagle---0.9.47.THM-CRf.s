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
% DateTime   : Thu Dec  3 10:21:29 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 113 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 232 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_669,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_672,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_22,c_669])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_171,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_353,plain,(
    ! [B_58,A_59] :
      ( v4_pre_topc(B_58,A_59)
      | k2_pre_topc(A_59,B_58) != B_58
      | ~ v2_pre_topc(A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_372,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_353])).

tff(c_389,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_372])).

tff(c_390,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_389])).

tff(c_391,plain,(
    ! [A_60,B_61] :
      ( k4_subset_1(u1_struct_0(A_60),B_61,k2_tops_1(A_60,B_61)) = k2_pre_topc(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_404,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_391])).

tff(c_420,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_404])).

tff(c_114,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_subset_1(A_36,B_37,C_38) = k4_xboole_0(B_37,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [C_39] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_39) = k4_xboole_0('#skF_2',C_39) ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_130,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_118])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_32,B_33] : k2_xboole_0(k4_xboole_0(A_32,B_33),A_32) = A_32 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_159,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_80])).

tff(c_133,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k7_subset_1(A_40,B_41,C_42),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_133])).

tff(c_146,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_282,plain,(
    ! [A_52,B_53,C_54] :
      ( k4_subset_1(A_52,B_53,C_54) = k2_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_622,plain,(
    ! [B_85] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_85,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_85,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_146,c_282])).

tff(c_647,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_622])).

tff(c_662,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_159,c_647])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_662])).

tff(c_666,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_673,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_666])).

tff(c_665,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_716,plain,(
    ! [A_98,B_99] :
      ( k2_pre_topc(A_98,B_99) = B_99
      | ~ v4_pre_topc(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_729,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_716])).

tff(c_739,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_665,c_729])).

tff(c_964,plain,(
    ! [A_132,B_133] :
      ( k7_subset_1(u1_struct_0(A_132),k2_pre_topc(A_132,B_133),k1_tops_1(A_132,B_133)) = k2_tops_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_976,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_964])).

tff(c_980,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_672,c_976])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.45  
% 2.85/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.45  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.85/1.45  
% 2.85/1.45  %Foreground sorts:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Background operators:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Foreground operators:
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.45  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.85/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.45  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.85/1.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.85/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.85/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.85/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.85/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.45  
% 3.15/1.47  tff(f_88, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 3.15/1.47  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/1.47  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.15/1.47  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 3.15/1.47  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.15/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.15/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.15/1.47  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.15/1.47  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.15/1.47  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.15/1.47  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.47  tff(c_669, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.47  tff(c_672, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_22, c_669])).
% 3.15/1.47  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.47  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 3.15/1.47  tff(c_28, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.47  tff(c_171, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_28])).
% 3.15/1.47  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.47  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.47  tff(c_353, plain, (![B_58, A_59]: (v4_pre_topc(B_58, A_59) | k2_pre_topc(A_59, B_58)!=B_58 | ~v2_pre_topc(A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.47  tff(c_372, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_353])).
% 3.15/1.47  tff(c_389, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_372])).
% 3.15/1.47  tff(c_390, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_171, c_389])).
% 3.15/1.47  tff(c_391, plain, (![A_60, B_61]: (k4_subset_1(u1_struct_0(A_60), B_61, k2_tops_1(A_60, B_61))=k2_pre_topc(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.47  tff(c_404, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_391])).
% 3.15/1.47  tff(c_420, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_404])).
% 3.15/1.47  tff(c_114, plain, (![A_36, B_37, C_38]: (k7_subset_1(A_36, B_37, C_38)=k4_xboole_0(B_37, C_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.47  tff(c_118, plain, (![C_39]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_39)=k4_xboole_0('#skF_2', C_39))), inference(resolution, [status(thm)], [c_22, c_114])).
% 3.15/1.47  tff(c_130, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_107, c_118])).
% 3.15/1.47  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_69, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_74, plain, (![A_32, B_33]: (k2_xboole_0(k4_xboole_0(A_32, B_33), A_32)=A_32)), inference(resolution, [status(thm)], [c_6, c_69])).
% 3.15/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_80, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(A_32, B_33))=A_32)), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 3.15/1.47  tff(c_159, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_130, c_80])).
% 3.15/1.47  tff(c_133, plain, (![A_40, B_41, C_42]: (m1_subset_1(k7_subset_1(A_40, B_41, C_42), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.47  tff(c_141, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_133])).
% 3.15/1.47  tff(c_146, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_141])).
% 3.15/1.47  tff(c_282, plain, (![A_52, B_53, C_54]: (k4_subset_1(A_52, B_53, C_54)=k2_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.47  tff(c_622, plain, (![B_85]: (k4_subset_1(u1_struct_0('#skF_1'), B_85, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_85, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_146, c_282])).
% 3.15/1.47  tff(c_647, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_622])).
% 3.15/1.47  tff(c_662, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_159, c_647])).
% 3.15/1.47  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_662])).
% 3.15/1.47  tff(c_666, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 3.15/1.47  tff(c_673, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_666])).
% 3.15/1.47  tff(c_665, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.15/1.47  tff(c_716, plain, (![A_98, B_99]: (k2_pre_topc(A_98, B_99)=B_99 | ~v4_pre_topc(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.47  tff(c_729, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_716])).
% 3.15/1.47  tff(c_739, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_665, c_729])).
% 3.15/1.47  tff(c_964, plain, (![A_132, B_133]: (k7_subset_1(u1_struct_0(A_132), k2_pre_topc(A_132, B_133), k1_tops_1(A_132, B_133))=k2_tops_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.47  tff(c_976, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_739, c_964])).
% 3.15/1.47  tff(c_980, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_672, c_976])).
% 3.15/1.47  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_673, c_980])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 220
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 2
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 8
% 3.15/1.47  #Demod        : 139
% 3.15/1.47  #Tautology    : 102
% 3.15/1.47  #SimpNegUnit  : 5
% 3.15/1.47  #BackRed      : 1
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.31
% 3.15/1.47  Parsing              : 0.17
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.39
% 3.15/1.47  Inferencing          : 0.14
% 3.15/1.47  Reduction            : 0.14
% 3.15/1.47  Demodulation         : 0.11
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.06
% 3.15/1.47  Abstraction          : 0.03
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.73
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
