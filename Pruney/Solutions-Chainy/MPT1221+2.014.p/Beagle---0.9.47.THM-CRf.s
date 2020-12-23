%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 237 expanded)
%              Number of leaves         :   31 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 415 expanded)
%              Number of equality atoms :   30 (  92 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_49,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_36,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_55,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_36])).

tff(c_56,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_30,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_104,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_49,c_30])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_26])).

tff(c_115,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_14,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_71,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [B_32] : k4_xboole_0(B_32,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_61])).

tff(c_87,plain,(
    ! [B_32] : k4_xboole_0(B_32,k1_xboole_0) = B_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_78])).

tff(c_121,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_124,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_121])).

tff(c_141,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k3_subset_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_13] :
      ( m1_subset_1(A_13,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_141])).

tff(c_153,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_162,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_subset_1(A_46,B_47,C_48) = k4_xboole_0(B_47,C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_13,C_48] : k7_subset_1(A_13,A_13,C_48) = k4_xboole_0(A_13,C_48) ),
    inference(resolution,[status(thm)],[c_153,c_162])).

tff(c_363,plain,(
    ! [B_68,A_69] :
      ( v4_pre_topc(B_68,A_69)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_69),k2_struct_0(A_69),B_68),A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_369,plain,(
    ! [B_68] :
      ( v4_pre_topc(B_68,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_68),'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_363])).

tff(c_373,plain,(
    ! [B_70] :
      ( v4_pre_topc(B_70,'#skF_1')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_70),'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_49,c_171,c_369])).

tff(c_390,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_373])).

tff(c_400,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_390])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_400])).

tff(c_404,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_403,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_467,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_478,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_467])).

tff(c_407,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(A_71,B_72) = B_72
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_411,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_407])).

tff(c_421,plain,(
    ! [A_74,B_75] : k2_xboole_0(A_74,k4_xboole_0(B_75,A_74)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_428,plain,(
    ! [B_75] : k4_xboole_0(B_75,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_411])).

tff(c_437,plain,(
    ! [B_75] : k4_xboole_0(B_75,k1_xboole_0) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_428])).

tff(c_476,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_467])).

tff(c_481,plain,(
    ! [A_87] : k3_subset_1(A_87,k1_xboole_0) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_476])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_487,plain,(
    ! [A_87] :
      ( m1_subset_1(A_87,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_10])).

tff(c_493,plain,(
    ! [A_87] : m1_subset_1(A_87,k1_zfmisc_1(A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_487])).

tff(c_533,plain,(
    ! [A_92,B_93,C_94] :
      ( k7_subset_1(A_92,B_93,C_94) = k4_xboole_0(B_93,C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_542,plain,(
    ! [A_87,C_94] : k7_subset_1(A_87,A_87,C_94) = k4_xboole_0(A_87,C_94) ),
    inference(resolution,[status(thm)],[c_493,c_533])).

tff(c_739,plain,(
    ! [A_116,B_117] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_116),k2_struct_0(A_116),B_117),A_116)
      | ~ v4_pre_topc(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_745,plain,(
    ! [B_117] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_117),'#skF_1')
      | ~ v4_pre_topc(B_117,'#skF_1')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_739])).

tff(c_758,plain,(
    ! [B_119] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_119),'#skF_1')
      | ~ v4_pre_topc(B_119,'#skF_1')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_49,c_542,c_745])).

tff(c_771,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_758])).

tff(c_782,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_403,c_771])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.61/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.41  
% 2.61/1.42  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.61/1.42  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.42  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.61/1.42  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.61/1.42  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.61/1.42  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.42  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.42  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.61/1.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.61/1.42  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.61/1.42  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.61/1.42  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.42  tff(c_24, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.61/1.42  tff(c_40, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.42  tff(c_45, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.61/1.42  tff(c_49, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.61/1.42  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.42  tff(c_55, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_36])).
% 2.61/1.42  tff(c_56, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_55])).
% 2.61/1.42  tff(c_30, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.42  tff(c_104, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_49, c_30])).
% 2.61/1.42  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.42  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_26])).
% 2.61/1.42  tff(c_115, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_122, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_115])).
% 2.61/1.42  tff(c_14, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.42  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.42  tff(c_57, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.42  tff(c_61, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.61/1.42  tff(c_71, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.42  tff(c_78, plain, (![B_32]: (k4_xboole_0(B_32, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_32))), inference(superposition, [status(thm), theory('equality')], [c_71, c_61])).
% 2.61/1.42  tff(c_87, plain, (![B_32]: (k4_xboole_0(B_32, k1_xboole_0)=B_32)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_78])).
% 2.61/1.42  tff(c_121, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_115])).
% 2.61/1.42  tff(c_124, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_121])).
% 2.61/1.42  tff(c_141, plain, (![A_43, B_44]: (m1_subset_1(k3_subset_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.42  tff(c_149, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_141])).
% 2.61/1.42  tff(c_153, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 2.61/1.42  tff(c_162, plain, (![A_46, B_47, C_48]: (k7_subset_1(A_46, B_47, C_48)=k4_xboole_0(B_47, C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.42  tff(c_171, plain, (![A_13, C_48]: (k7_subset_1(A_13, A_13, C_48)=k4_xboole_0(A_13, C_48))), inference(resolution, [status(thm)], [c_153, c_162])).
% 2.61/1.42  tff(c_363, plain, (![B_68, A_69]: (v4_pre_topc(B_68, A_69) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_69), k2_struct_0(A_69), B_68), A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.61/1.42  tff(c_369, plain, (![B_68]: (v4_pre_topc(B_68, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_68), '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_363])).
% 2.61/1.42  tff(c_373, plain, (![B_70]: (v4_pre_topc(B_70, '#skF_1') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_70), '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_49, c_171, c_369])).
% 2.61/1.42  tff(c_390, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_122, c_373])).
% 2.61/1.42  tff(c_400, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_390])).
% 2.61/1.42  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_400])).
% 2.61/1.42  tff(c_404, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_55])).
% 2.61/1.42  tff(c_403, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_55])).
% 2.61/1.42  tff(c_467, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_478, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_467])).
% 2.61/1.42  tff(c_407, plain, (![A_71, B_72]: (k2_xboole_0(A_71, B_72)=B_72 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.42  tff(c_411, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_407])).
% 2.61/1.42  tff(c_421, plain, (![A_74, B_75]: (k2_xboole_0(A_74, k4_xboole_0(B_75, A_74))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.42  tff(c_428, plain, (![B_75]: (k4_xboole_0(B_75, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_75))), inference(superposition, [status(thm), theory('equality')], [c_421, c_411])).
% 2.61/1.42  tff(c_437, plain, (![B_75]: (k4_xboole_0(B_75, k1_xboole_0)=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_428])).
% 2.61/1.42  tff(c_476, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_467])).
% 2.61/1.42  tff(c_481, plain, (![A_87]: (k3_subset_1(A_87, k1_xboole_0)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_476])).
% 2.61/1.42  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.42  tff(c_487, plain, (![A_87]: (m1_subset_1(A_87, k1_zfmisc_1(A_87)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_481, c_10])).
% 2.61/1.42  tff(c_493, plain, (![A_87]: (m1_subset_1(A_87, k1_zfmisc_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_487])).
% 2.61/1.42  tff(c_533, plain, (![A_92, B_93, C_94]: (k7_subset_1(A_92, B_93, C_94)=k4_xboole_0(B_93, C_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.42  tff(c_542, plain, (![A_87, C_94]: (k7_subset_1(A_87, A_87, C_94)=k4_xboole_0(A_87, C_94))), inference(resolution, [status(thm)], [c_493, c_533])).
% 2.61/1.42  tff(c_739, plain, (![A_116, B_117]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_116), k2_struct_0(A_116), B_117), A_116) | ~v4_pre_topc(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.61/1.42  tff(c_745, plain, (![B_117]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_117), '#skF_1') | ~v4_pre_topc(B_117, '#skF_1') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_739])).
% 2.61/1.42  tff(c_758, plain, (![B_119]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_119), '#skF_1') | ~v4_pre_topc(B_119, '#skF_1') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_49, c_542, c_745])).
% 2.61/1.42  tff(c_771, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_478, c_758])).
% 2.61/1.42  tff(c_782, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_403, c_771])).
% 2.61/1.42  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_782])).
% 2.61/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  Inference rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Ref     : 0
% 2.61/1.42  #Sup     : 173
% 2.61/1.42  #Fact    : 0
% 2.61/1.42  #Define  : 0
% 2.61/1.42  #Split   : 5
% 2.61/1.42  #Chain   : 0
% 2.61/1.42  #Close   : 0
% 2.61/1.42  
% 2.61/1.42  Ordering : KBO
% 2.61/1.42  
% 2.61/1.42  Simplification rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Subsume      : 5
% 2.61/1.42  #Demod        : 100
% 2.61/1.42  #Tautology    : 100
% 2.61/1.42  #SimpNegUnit  : 3
% 2.61/1.42  #BackRed      : 1
% 2.61/1.42  
% 2.61/1.42  #Partial instantiations: 0
% 2.61/1.42  #Strategies tried      : 1
% 2.61/1.43  
% 2.61/1.43  Timing (in seconds)
% 2.61/1.43  ----------------------
% 2.61/1.43  Preprocessing        : 0.30
% 2.61/1.43  Parsing              : 0.16
% 2.61/1.43  CNF conversion       : 0.02
% 2.61/1.43  Main loop            : 0.33
% 2.61/1.43  Inferencing          : 0.13
% 2.61/1.43  Reduction            : 0.11
% 2.61/1.43  Demodulation         : 0.08
% 2.61/1.43  BG Simplification    : 0.02
% 2.61/1.43  Subsumption          : 0.05
% 2.61/1.43  Abstraction          : 0.02
% 2.61/1.43  MUC search           : 0.00
% 2.61/1.43  Cooper               : 0.00
% 2.61/1.43  Total                : 0.67
% 2.61/1.43  Index Insertion      : 0.00
% 2.61/1.43  Index Deletion       : 0.00
% 2.61/1.43  Index Matching       : 0.00
% 2.61/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
