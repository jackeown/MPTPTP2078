%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 161 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 360 expanded)
%              Number of equality atoms :   32 (  94 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_tops_1(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] :
      ( k7_subset_1(A_2,B_3,C_4) = k4_xboole_0(B_3,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_30,B_31,C_32] :
      ( k7_subset_1(u1_struct_0(A_30),k2_tops_1(A_30,B_31),C_32) = k4_xboole_0(k2_tops_1(A_30,B_31),C_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_96,plain,(
    ! [C_32] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_32) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_32)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_92])).

tff(c_100,plain,(
    ! [C_32] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_32) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_96])).

tff(c_20,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k2_pre_topc(A_26,k2_tops_1(A_26,B_27)) = k2_tops_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_68,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_64])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( k7_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_29),k1_tops_1(A_28,B_29)) = k2_tops_1(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_73])).

tff(c_89,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_140,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_89])).

tff(c_141,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_145,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_145])).

tff(c_151,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_14,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_22,B_23,C_4] :
      ( k7_subset_1(u1_struct_0(A_22),k2_tops_1(A_22,B_23),C_4) = k4_xboole_0(k2_tops_1(A_22,B_23),C_4)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_155,plain,(
    ! [C_4] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_4) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_4)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_151,c_46])).

tff(c_167,plain,(
    ! [C_4] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_4) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_155])).

tff(c_47,plain,(
    ! [A_24,B_25] :
      ( k1_tops_1(A_24,k2_tops_1(A_24,k2_tops_1(A_24,B_25))) = k1_xboole_0
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_55,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_51])).

tff(c_122,plain,(
    ! [A_36,B_37] :
      ( k2_pre_topc(A_36,k2_tops_1(A_36,k2_tops_1(A_36,B_37))) = k2_tops_1(A_36,k2_tops_1(A_36,B_37))
      | ~ v2_pre_topc(A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_126,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_122])).

tff(c_130,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_126])).

tff(c_8,plain,(
    ! [A_7,B_9] :
      ( k7_subset_1(u1_struct_0(A_7),k2_pre_topc(A_7,B_9),k1_tops_1(A_7,B_9)) = k2_tops_1(A_7,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_8])).

tff(c_138,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_55,c_134])).

tff(c_265,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_167,c_138])).

tff(c_266,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_265])).

tff(c_269,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_151,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  %$ m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.33  
% 2.21/1.33  %Foreground sorts:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Background operators:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Foreground operators:
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.33  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.21/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.21/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.33  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.21/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.21/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.33  
% 2.21/1.35  tff(f_72, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 2.21/1.35  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.21/1.35  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.21/1.35  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k2_tops_1(A, B)) = k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l79_tops_1)).
% 2.21/1.35  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.21/1.35  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.21/1.35  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 2.21/1.35  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k2_tops_1(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.35  tff(c_43, plain, (![A_22, B_23]: (m1_subset_1(k2_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.35  tff(c_4, plain, (![A_2, B_3, C_4]: (k7_subset_1(A_2, B_3, C_4)=k4_xboole_0(B_3, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.35  tff(c_92, plain, (![A_30, B_31, C_32]: (k7_subset_1(u1_struct_0(A_30), k2_tops_1(A_30, B_31), C_32)=k4_xboole_0(k2_tops_1(A_30, B_31), C_32) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_43, c_4])).
% 2.21/1.35  tff(c_96, plain, (![C_32]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_32)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_32) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_92])).
% 2.21/1.35  tff(c_100, plain, (![C_32]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_32)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_32))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_96])).
% 2.21/1.35  tff(c_20, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_60, plain, (![A_26, B_27]: (k2_pre_topc(A_26, k2_tops_1(A_26, B_27))=k2_tops_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.35  tff(c_64, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_60])).
% 2.21/1.35  tff(c_68, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_64])).
% 2.21/1.35  tff(c_73, plain, (![A_28, B_29]: (k7_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_29), k1_tops_1(A_28, B_29))=k2_tops_1(A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.35  tff(c_82, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_73])).
% 2.21/1.35  tff(c_89, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82])).
% 2.21/1.35  tff(c_140, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_89])).
% 2.21/1.35  tff(c_141, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_140])).
% 2.21/1.35  tff(c_145, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_141])).
% 2.21/1.35  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_145])).
% 2.21/1.35  tff(c_151, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_140])).
% 2.21/1.35  tff(c_14, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.35  tff(c_46, plain, (![A_22, B_23, C_4]: (k7_subset_1(u1_struct_0(A_22), k2_tops_1(A_22, B_23), C_4)=k4_xboole_0(k2_tops_1(A_22, B_23), C_4) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_43, c_4])).
% 2.21/1.35  tff(c_155, plain, (![C_4]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_4)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_4) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_151, c_46])).
% 2.21/1.35  tff(c_167, plain, (![C_4]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_4)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_4))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_155])).
% 2.21/1.35  tff(c_47, plain, (![A_24, B_25]: (k1_tops_1(A_24, k2_tops_1(A_24, k2_tops_1(A_24, B_25)))=k1_xboole_0 | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.21/1.35  tff(c_51, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_47])).
% 2.21/1.35  tff(c_55, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_51])).
% 2.21/1.35  tff(c_122, plain, (![A_36, B_37]: (k2_pre_topc(A_36, k2_tops_1(A_36, k2_tops_1(A_36, B_37)))=k2_tops_1(A_36, k2_tops_1(A_36, B_37)) | ~v2_pre_topc(A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.21/1.35  tff(c_126, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_122])).
% 2.21/1.35  tff(c_130, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_126])).
% 2.21/1.35  tff(c_8, plain, (![A_7, B_9]: (k7_subset_1(u1_struct_0(A_7), k2_pre_topc(A_7, B_9), k1_tops_1(A_7, B_9))=k2_tops_1(A_7, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.35  tff(c_134, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_130, c_8])).
% 2.21/1.35  tff(c_138, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_55, c_134])).
% 2.21/1.35  tff(c_265, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_167, c_138])).
% 2.21/1.35  tff(c_266, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_14, c_265])).
% 2.21/1.35  tff(c_269, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_266])).
% 2.21/1.35  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_151, c_269])).
% 2.21/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  Inference rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Ref     : 0
% 2.21/1.35  #Sup     : 58
% 2.21/1.35  #Fact    : 0
% 2.21/1.35  #Define  : 0
% 2.21/1.35  #Split   : 2
% 2.21/1.35  #Chain   : 0
% 2.21/1.35  #Close   : 0
% 2.21/1.35  
% 2.21/1.35  Ordering : KBO
% 2.21/1.35  
% 2.21/1.35  Simplification rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Subsume      : 0
% 2.21/1.35  #Demod        : 46
% 2.21/1.35  #Tautology    : 36
% 2.21/1.35  #SimpNegUnit  : 1
% 2.21/1.35  #BackRed      : 0
% 2.21/1.35  
% 2.21/1.35  #Partial instantiations: 0
% 2.21/1.35  #Strategies tried      : 1
% 2.21/1.35  
% 2.21/1.35  Timing (in seconds)
% 2.21/1.35  ----------------------
% 2.21/1.35  Preprocessing        : 0.32
% 2.21/1.35  Parsing              : 0.17
% 2.21/1.35  CNF conversion       : 0.02
% 2.21/1.35  Main loop            : 0.20
% 2.21/1.35  Inferencing          : 0.08
% 2.21/1.35  Reduction            : 0.07
% 2.21/1.35  Demodulation         : 0.05
% 2.21/1.35  BG Simplification    : 0.01
% 2.21/1.35  Subsumption          : 0.03
% 2.21/1.35  Abstraction          : 0.02
% 2.21/1.35  MUC search           : 0.00
% 2.21/1.35  Cooper               : 0.00
% 2.21/1.35  Total                : 0.55
% 2.21/1.35  Index Insertion      : 0.00
% 2.21/1.35  Index Deletion       : 0.00
% 2.21/1.35  Index Matching       : 0.00
% 2.21/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
