%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:21 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 162 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 306 expanded)
%              Number of equality atoms :   53 ( 116 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_45,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2045,plain,(
    ! [A_157,B_158,C_159] :
      ( k7_subset_1(A_157,B_158,C_159) = k4_xboole_0(B_158,C_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2048,plain,(
    ! [C_159] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_159) = k4_xboole_0('#skF_2',C_159) ),
    inference(resolution,[status(thm)],[c_30,c_2045])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_162,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1391,plain,(
    ! [B_92,A_93] :
      ( v4_pre_topc(B_92,A_93)
      | k2_pre_topc(A_93,B_92) != B_92
      | ~ v2_pre_topc(A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1397,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1391])).

tff(c_1401,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_1397])).

tff(c_1402,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_1401])).

tff(c_1425,plain,(
    ! [A_97,B_98] :
      ( k4_subset_1(u1_struct_0(A_97),B_98,k2_tops_1(A_97,B_98)) = k2_pre_topc(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1429,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1425])).

tff(c_1433,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1429])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [B_43,A_44] : k3_tarski(k2_tarski(B_43,A_44)) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_10])).

tff(c_406,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(A_60,B_61,C_62) = k4_xboole_0(B_61,C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_410,plain,(
    ! [C_63] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_63) = k4_xboole_0('#skF_2',C_63) ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_278,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_42])).

tff(c_416,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_278])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_428,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_449,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_428])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_677,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_6])).

tff(c_683,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_169,c_677])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1216,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1504,plain,(
    ! [A_115,B_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_117)) = k2_xboole_0(B_116,k2_tops_1(A_115,B_117))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_22,c_1216])).

tff(c_1508,plain,(
    ! [B_117] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_117)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1504])).

tff(c_1513,plain,(
    ! [B_118] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_118)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1508])).

tff(c_1520,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_1513])).

tff(c_1525,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_683,c_1520])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_1525])).

tff(c_1528,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1530,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1528,c_1530])).

tff(c_1743,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2049,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_1743])).

tff(c_1529,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2343,plain,(
    ! [A_167,B_168] :
      ( k2_pre_topc(A_167,B_168) = B_168
      | ~ v4_pre_topc(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2349,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2343])).

tff(c_2353,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1529,c_2349])).

tff(c_2868,plain,(
    ! [A_193,B_194] :
      ( k7_subset_1(u1_struct_0(A_193),k2_pre_topc(A_193,B_194),k1_tops_1(A_193,B_194)) = k2_tops_1(A_193,B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2877,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_2868])).

tff(c_2881,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2048,c_2877])).

tff(c_2883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2049,c_2881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.84  
% 4.27/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.84  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.27/1.84  
% 4.27/1.84  %Foreground sorts:
% 4.27/1.84  
% 4.27/1.84  
% 4.27/1.84  %Background operators:
% 4.27/1.84  
% 4.27/1.84  
% 4.27/1.84  %Foreground operators:
% 4.27/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.27/1.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.27/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.27/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.27/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.27/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.27/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.84  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.27/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.27/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.27/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.27/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.27/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.27/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.27/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.27/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.27/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.27/1.84  
% 4.27/1.85  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.27/1.85  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.27/1.85  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.27/1.85  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.27/1.85  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.27/1.85  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.27/1.85  tff(f_29, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.27/1.85  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 4.27/1.85  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.27/1.85  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.27/1.85  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.27/1.85  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.27/1.85  tff(c_2045, plain, (![A_157, B_158, C_159]: (k7_subset_1(A_157, B_158, C_159)=k4_xboole_0(B_158, C_159) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.85  tff(c_2048, plain, (![C_159]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_159)=k4_xboole_0('#skF_2', C_159))), inference(resolution, [status(thm)], [c_30, c_2045])).
% 4.27/1.85  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.27/1.85  tff(c_162, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 4.27/1.85  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.27/1.85  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.27/1.85  tff(c_1391, plain, (![B_92, A_93]: (v4_pre_topc(B_92, A_93) | k2_pre_topc(A_93, B_92)!=B_92 | ~v2_pre_topc(A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.27/1.85  tff(c_1397, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1391])).
% 4.27/1.85  tff(c_1401, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_1397])).
% 4.27/1.85  tff(c_1402, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_162, c_1401])).
% 4.27/1.85  tff(c_1425, plain, (![A_97, B_98]: (k4_subset_1(u1_struct_0(A_97), B_98, k2_tops_1(A_97, B_98))=k2_pre_topc(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.27/1.85  tff(c_1429, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1425])).
% 4.27/1.85  tff(c_1433, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1429])).
% 4.27/1.85  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.27/1.85  tff(c_91, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.85  tff(c_163, plain, (![B_43, A_44]: (k3_tarski(k2_tarski(B_43, A_44))=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_91])).
% 4.27/1.85  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.85  tff(c_169, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_163, c_10])).
% 4.27/1.85  tff(c_406, plain, (![A_60, B_61, C_62]: (k7_subset_1(A_60, B_61, C_62)=k4_xboole_0(B_61, C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.85  tff(c_410, plain, (![C_63]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_63)=k4_xboole_0('#skF_2', C_63))), inference(resolution, [status(thm)], [c_30, c_406])).
% 4.27/1.85  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.27/1.85  tff(c_278, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_162, c_42])).
% 4.27/1.85  tff(c_416, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_410, c_278])).
% 4.27/1.85  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.27/1.85  tff(c_428, plain, (k2_xboole_0(k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 4.27/1.85  tff(c_449, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_169, c_428])).
% 4.27/1.85  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.85  tff(c_677, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_449, c_6])).
% 4.27/1.85  tff(c_683, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_449, c_169, c_677])).
% 4.27/1.85  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(k2_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.27/1.85  tff(c_1216, plain, (![A_84, B_85, C_86]: (k4_subset_1(A_84, B_85, C_86)=k2_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.85  tff(c_1504, plain, (![A_115, B_116, B_117]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_117))=k2_xboole_0(B_116, k2_tops_1(A_115, B_117)) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_22, c_1216])).
% 4.27/1.85  tff(c_1508, plain, (![B_117]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_117))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1504])).
% 4.27/1.85  tff(c_1513, plain, (![B_118]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_118))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1508])).
% 4.27/1.85  tff(c_1520, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1513])).
% 4.27/1.85  tff(c_1525, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_683, c_1520])).
% 4.27/1.85  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1402, c_1525])).
% 4.27/1.85  tff(c_1528, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 4.27/1.85  tff(c_1530, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 4.27/1.85  tff(c_1741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1528, c_1530])).
% 4.27/1.85  tff(c_1743, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.27/1.85  tff(c_2049, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_1743])).
% 4.27/1.85  tff(c_1529, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 4.27/1.85  tff(c_2343, plain, (![A_167, B_168]: (k2_pre_topc(A_167, B_168)=B_168 | ~v4_pre_topc(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.27/1.85  tff(c_2349, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2343])).
% 4.27/1.85  tff(c_2353, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1529, c_2349])).
% 4.27/1.85  tff(c_2868, plain, (![A_193, B_194]: (k7_subset_1(u1_struct_0(A_193), k2_pre_topc(A_193, B_194), k1_tops_1(A_193, B_194))=k2_tops_1(A_193, B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.27/1.85  tff(c_2877, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_2868])).
% 4.27/1.85  tff(c_2881, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2048, c_2877])).
% 4.27/1.85  tff(c_2883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2049, c_2881])).
% 4.27/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.85  
% 4.27/1.85  Inference rules
% 4.27/1.85  ----------------------
% 4.27/1.85  #Ref     : 0
% 4.27/1.85  #Sup     : 684
% 4.27/1.85  #Fact    : 0
% 4.27/1.85  #Define  : 0
% 4.27/1.85  #Split   : 3
% 4.27/1.85  #Chain   : 0
% 4.27/1.85  #Close   : 0
% 4.27/1.85  
% 4.27/1.85  Ordering : KBO
% 4.27/1.85  
% 4.27/1.85  Simplification rules
% 4.27/1.85  ----------------------
% 4.27/1.85  #Subsume      : 40
% 4.27/1.85  #Demod        : 1072
% 4.27/1.85  #Tautology    : 571
% 4.27/1.85  #SimpNegUnit  : 5
% 4.27/1.85  #BackRed      : 3
% 4.27/1.85  
% 4.27/1.85  #Partial instantiations: 0
% 4.27/1.85  #Strategies tried      : 1
% 4.27/1.85  
% 4.27/1.85  Timing (in seconds)
% 4.27/1.85  ----------------------
% 4.27/1.86  Preprocessing        : 0.39
% 4.27/1.86  Parsing              : 0.22
% 4.27/1.86  CNF conversion       : 0.02
% 4.27/1.86  Main loop            : 0.68
% 4.27/1.86  Inferencing          : 0.20
% 4.27/1.86  Reduction            : 0.34
% 4.27/1.86  Demodulation         : 0.29
% 4.27/1.86  BG Simplification    : 0.03
% 4.27/1.86  Subsumption          : 0.08
% 4.27/1.86  Abstraction          : 0.04
% 4.27/1.86  MUC search           : 0.00
% 4.27/1.86  Cooper               : 0.00
% 4.27/1.86  Total                : 1.10
% 4.27/1.86  Index Insertion      : 0.00
% 4.27/1.86  Index Deletion       : 0.00
% 4.27/1.86  Index Matching       : 0.00
% 4.27/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
