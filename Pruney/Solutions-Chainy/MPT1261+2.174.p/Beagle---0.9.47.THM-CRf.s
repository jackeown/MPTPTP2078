%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 125 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 254 expanded)
%              Number of equality atoms :   49 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6385,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_subset_1(A_194,B_195,C_196) = k4_xboole_0(B_195,C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6388,plain,(
    ! [C_196] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_196) = k4_xboole_0('#skF_2',C_196) ),
    inference(resolution,[status(thm)],[c_28,c_6385])).

tff(c_34,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_867,plain,(
    ! [B_85,A_86] :
      ( v4_pre_topc(B_85,A_86)
      | k2_pre_topc(A_86,B_85) != B_85
      | ~ v2_pre_topc(A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_873,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_867])).

tff(c_877,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_873])).

tff(c_878,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_877])).

tff(c_888,plain,(
    ! [A_87,B_88] :
      ( k4_subset_1(u1_struct_0(A_87),B_88,k2_tops_1(A_87,B_88)) = k2_pre_topc(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_892,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_888])).

tff(c_896,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_892])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_subset_1(A_46,B_47,C_48) = k4_xboole_0(B_47,C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [C_48] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_48) = k4_xboole_0('#skF_2',C_48) ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_169,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_40])).

tff(c_170,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_169])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k4_xboole_0(A_41,B_42),C_43)
      | ~ r1_tarski(A_41,k2_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_xboole_0(k4_xboole_0(A_52,B_53),C_54) = C_54
      | ~ r1_tarski(A_52,k2_xboole_0(B_53,C_54)) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_165,plain,(
    ! [A_52,A_3] :
      ( k2_xboole_0(k4_xboole_0(A_52,A_3),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_52,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_148])).

tff(c_205,plain,(
    ! [A_55,A_56] :
      ( k4_xboole_0(A_55,A_56) = k1_xboole_0
      | ~ r1_tarski(A_55,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_165])).

tff(c_228,plain,(
    ! [A_57,B_58] : k4_xboole_0(k4_xboole_0(A_57,B_58),A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_205])).

tff(c_256,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_228])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_312,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_323,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_312])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_836,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_subset_1(A_81,B_82,C_83) = k2_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5653,plain,(
    ! [A_174,B_175,B_176] :
      ( k4_subset_1(u1_struct_0(A_174),B_175,k2_tops_1(A_174,B_176)) = k2_xboole_0(B_175,k2_tops_1(A_174,B_176))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_20,c_836])).

tff(c_5657,plain,(
    ! [B_176] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_176)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_176))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_5653])).

tff(c_6326,plain,(
    ! [B_184] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_184)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_184))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5657])).

tff(c_6333,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_6326])).

tff(c_6338,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_323,c_6333])).

tff(c_6340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_6338])).

tff(c_6341,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6389,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6388,c_6341])).

tff(c_6342,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6556,plain,(
    ! [A_212,B_213] :
      ( k2_pre_topc(A_212,B_213) = B_213
      | ~ v4_pre_topc(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6559,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_6556])).

tff(c_6562,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6342,c_6559])).

tff(c_7139,plain,(
    ! [A_239,B_240] :
      ( k7_subset_1(u1_struct_0(A_239),k2_pre_topc(A_239,B_240),k1_tops_1(A_239,B_240)) = k2_tops_1(A_239,B_240)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7148,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6562,c_7139])).

tff(c_7152,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_6388,c_7148])).

tff(c_7154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6389,c_7152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.06  
% 5.16/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.06  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.16/2.06  
% 5.16/2.06  %Foreground sorts:
% 5.16/2.06  
% 5.16/2.06  
% 5.16/2.06  %Background operators:
% 5.16/2.06  
% 5.16/2.06  
% 5.16/2.06  %Foreground operators:
% 5.16/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/2.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.16/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.16/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/2.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.16/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.16/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.16/2.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.16/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.16/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.16/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.16/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.16/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.16/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.16/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.16/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/2.06  
% 5.16/2.07  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.16/2.07  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.16/2.07  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.16/2.07  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.16/2.07  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.16/2.07  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.16/2.07  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.16/2.07  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.16/2.07  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.16/2.07  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.16/2.07  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.16/2.07  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.16/2.07  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.16/2.07  tff(c_6385, plain, (![A_194, B_195, C_196]: (k7_subset_1(A_194, B_195, C_196)=k4_xboole_0(B_195, C_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.16/2.07  tff(c_6388, plain, (![C_196]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_196)=k4_xboole_0('#skF_2', C_196))), inference(resolution, [status(thm)], [c_28, c_6385])).
% 5.16/2.07  tff(c_34, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.16/2.07  tff(c_92, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 5.16/2.07  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.16/2.07  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.16/2.07  tff(c_867, plain, (![B_85, A_86]: (v4_pre_topc(B_85, A_86) | k2_pre_topc(A_86, B_85)!=B_85 | ~v2_pre_topc(A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.16/2.07  tff(c_873, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_867])).
% 5.16/2.07  tff(c_877, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_873])).
% 5.16/2.07  tff(c_878, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_92, c_877])).
% 5.16/2.07  tff(c_888, plain, (![A_87, B_88]: (k4_subset_1(u1_struct_0(A_87), B_88, k2_tops_1(A_87, B_88))=k2_pre_topc(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.16/2.07  tff(c_892, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_888])).
% 5.16/2.07  tff(c_896, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_892])).
% 5.16/2.07  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.07  tff(c_126, plain, (![A_46, B_47, C_48]: (k7_subset_1(A_46, B_47, C_48)=k4_xboole_0(B_47, C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.16/2.07  tff(c_129, plain, (![C_48]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_48)=k4_xboole_0('#skF_2', C_48))), inference(resolution, [status(thm)], [c_28, c_126])).
% 5.16/2.07  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.16/2.07  tff(c_169, plain, (v4_pre_topc('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_40])).
% 5.16/2.07  tff(c_170, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92, c_169])).
% 5.16/2.07  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.16/2.08  tff(c_107, plain, (![A_41, B_42, C_43]: (r1_tarski(k4_xboole_0(A_41, B_42), C_43) | ~r1_tarski(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.16/2.08  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.16/2.08  tff(c_148, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k4_xboole_0(A_52, B_53), C_54)=C_54 | ~r1_tarski(A_52, k2_xboole_0(B_53, C_54)))), inference(resolution, [status(thm)], [c_107, c_2])).
% 5.16/2.08  tff(c_165, plain, (![A_52, A_3]: (k2_xboole_0(k4_xboole_0(A_52, A_3), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_52, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_148])).
% 5.16/2.08  tff(c_205, plain, (![A_55, A_56]: (k4_xboole_0(A_55, A_56)=k1_xboole_0 | ~r1_tarski(A_55, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_165])).
% 5.16/2.08  tff(c_228, plain, (![A_57, B_58]: (k4_xboole_0(k4_xboole_0(A_57, B_58), A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_205])).
% 5.16/2.08  tff(c_256, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_170, c_228])).
% 5.16/2.08  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.16/2.08  tff(c_312, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_8])).
% 5.16/2.08  tff(c_323, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_312])).
% 5.16/2.08  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(k2_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.16/2.08  tff(c_836, plain, (![A_81, B_82, C_83]: (k4_subset_1(A_81, B_82, C_83)=k2_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.16/2.08  tff(c_5653, plain, (![A_174, B_175, B_176]: (k4_subset_1(u1_struct_0(A_174), B_175, k2_tops_1(A_174, B_176))=k2_xboole_0(B_175, k2_tops_1(A_174, B_176)) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_20, c_836])).
% 5.16/2.08  tff(c_5657, plain, (![B_176]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_176))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_176)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_5653])).
% 5.16/2.08  tff(c_6326, plain, (![B_184]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_184))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_184)) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5657])).
% 5.16/2.08  tff(c_6333, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_6326])).
% 5.16/2.08  tff(c_6338, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_896, c_323, c_6333])).
% 5.16/2.08  tff(c_6340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_6338])).
% 5.16/2.08  tff(c_6341, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 5.16/2.08  tff(c_6389, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6388, c_6341])).
% 5.16/2.08  tff(c_6342, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 5.16/2.08  tff(c_6556, plain, (![A_212, B_213]: (k2_pre_topc(A_212, B_213)=B_213 | ~v4_pre_topc(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.16/2.08  tff(c_6559, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_6556])).
% 5.16/2.08  tff(c_6562, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6342, c_6559])).
% 5.16/2.08  tff(c_7139, plain, (![A_239, B_240]: (k7_subset_1(u1_struct_0(A_239), k2_pre_topc(A_239, B_240), k1_tops_1(A_239, B_240))=k2_tops_1(A_239, B_240) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.16/2.08  tff(c_7148, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6562, c_7139])).
% 5.16/2.08  tff(c_7152, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_6388, c_7148])).
% 5.16/2.08  tff(c_7154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6389, c_7152])).
% 5.16/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.08  
% 5.16/2.08  Inference rules
% 5.16/2.08  ----------------------
% 5.16/2.08  #Ref     : 0
% 5.16/2.08  #Sup     : 1644
% 5.16/2.08  #Fact    : 0
% 5.16/2.08  #Define  : 0
% 5.16/2.08  #Split   : 4
% 5.16/2.08  #Chain   : 0
% 5.16/2.08  #Close   : 0
% 5.16/2.08  
% 5.16/2.08  Ordering : KBO
% 5.16/2.08  
% 5.16/2.08  Simplification rules
% 5.16/2.08  ----------------------
% 5.16/2.08  #Subsume      : 178
% 5.16/2.08  #Demod        : 1818
% 5.16/2.08  #Tautology    : 1166
% 5.16/2.08  #SimpNegUnit  : 4
% 5.16/2.08  #BackRed      : 5
% 5.16/2.08  
% 5.16/2.08  #Partial instantiations: 0
% 5.16/2.08  #Strategies tried      : 1
% 5.16/2.08  
% 5.16/2.08  Timing (in seconds)
% 5.16/2.08  ----------------------
% 5.16/2.08  Preprocessing        : 0.33
% 5.16/2.08  Parsing              : 0.18
% 5.16/2.08  CNF conversion       : 0.02
% 5.16/2.08  Main loop            : 0.95
% 5.16/2.08  Inferencing          : 0.31
% 5.16/2.08  Reduction            : 0.41
% 5.16/2.08  Demodulation         : 0.32
% 5.16/2.08  BG Simplification    : 0.03
% 5.16/2.08  Subsumption          : 0.15
% 5.16/2.08  Abstraction          : 0.06
% 5.16/2.08  MUC search           : 0.00
% 5.16/2.08  Cooper               : 0.00
% 5.16/2.08  Total                : 1.31
% 5.16/2.08  Index Insertion      : 0.00
% 5.16/2.08  Index Deletion       : 0.00
% 5.16/2.08  Index Matching       : 0.00
% 5.16/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
