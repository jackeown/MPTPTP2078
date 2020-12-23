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
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 162 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 219 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_89,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_39,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_subset_1(A_8,B_9,k3_subset_1(A_8,B_9)) = k2_subset_1(A_8)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( k4_subset_1(A_43,B_44,k3_subset_1(A_43,B_44)) = A_43
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_124,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,k3_subset_1(A_10,k1_xboole_0)) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_129,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_124])).

tff(c_243,plain,(
    ! [A_63,B_64] :
      ( k4_subset_1(u1_struct_0(A_63),B_64,k3_subset_1(u1_struct_0(A_63),B_64)) = k2_struct_0(A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_257,plain,(
    ! [A_63] :
      ( k4_subset_1(u1_struct_0(A_63),k1_xboole_0,u1_struct_0(A_63)) = k2_struct_0(A_63)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_243])).

tff(c_264,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129,c_257])).

tff(c_269,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_273,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_269])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_188,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(B_56,A_57)
      | ~ v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [A_57] :
      ( v4_pre_topc(k1_xboole_0,A_57)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_16,c_188])).

tff(c_206,plain,(
    ! [A_58] :
      ( v4_pre_topc(k1_xboole_0,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_159,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = B_50
      | ~ v4_pre_topc(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_174,plain,(
    ! [A_49] :
      ( k2_pre_topc(A_49,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_227,plain,(
    ! [A_61] :
      ( k2_pre_topc(A_61,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_206,c_174])).

tff(c_230,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_227])).

tff(c_233,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_230])).

tff(c_94,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k3_subset_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_94])).

tff(c_109,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_72,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_76,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_74])).

tff(c_312,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k3_subset_1(u1_struct_0(A_67),B_68))) = k1_tops_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_343,plain,(
    ! [A_67] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k1_xboole_0)) = k1_tops_1(A_67,u1_struct_0(A_67))
      | ~ m1_subset_1(u1_struct_0(A_67),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_312])).

tff(c_426,plain,(
    ! [A_71] :
      ( k3_subset_1(u1_struct_0(A_71),k2_pre_topc(A_71,k1_xboole_0)) = k1_tops_1(A_71,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_343])).

tff(c_447,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_426])).

tff(c_454,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_273,c_39,c_233,c_447])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.37  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.44/1.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.44/1.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.44/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.44/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.44/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.44/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.44/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.44/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.37  
% 2.44/1.39  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.44/1.39  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.44/1.39  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.44/1.39  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.44/1.39  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.44/1.39  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.44/1.39  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.44/1.39  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.44/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.39  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.44/1.39  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.44/1.39  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.44/1.39  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.44/1.39  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.44/1.39  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.39  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.39  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.44/1.39  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.44/1.39  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.44/1.39  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.44/1.39  tff(c_12, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.39  tff(c_37, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.44/1.39  tff(c_39, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_37])).
% 2.44/1.39  tff(c_14, plain, (![A_8, B_9]: (k4_subset_1(A_8, B_9, k3_subset_1(A_8, B_9))=k2_subset_1(A_8) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.39  tff(c_118, plain, (![A_43, B_44]: (k4_subset_1(A_43, B_44, k3_subset_1(A_43, B_44))=A_43 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.44/1.39  tff(c_124, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, k3_subset_1(A_10, k1_xboole_0))=A_10)), inference(resolution, [status(thm)], [c_16, c_118])).
% 2.44/1.39  tff(c_129, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_124])).
% 2.44/1.39  tff(c_243, plain, (![A_63, B_64]: (k4_subset_1(u1_struct_0(A_63), B_64, k3_subset_1(u1_struct_0(A_63), B_64))=k2_struct_0(A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.39  tff(c_257, plain, (![A_63]: (k4_subset_1(u1_struct_0(A_63), k1_xboole_0, u1_struct_0(A_63))=k2_struct_0(A_63) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_39, c_243])).
% 2.44/1.39  tff(c_264, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_129, c_257])).
% 2.44/1.39  tff(c_269, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_22, c_264])).
% 2.44/1.39  tff(c_273, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_269])).
% 2.44/1.39  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.44/1.39  tff(c_188, plain, (![B_56, A_57]: (v4_pre_topc(B_56, A_57) | ~v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.39  tff(c_200, plain, (![A_57]: (v4_pre_topc(k1_xboole_0, A_57) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(resolution, [status(thm)], [c_16, c_188])).
% 2.44/1.39  tff(c_206, plain, (![A_58]: (v4_pre_topc(k1_xboole_0, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_200])).
% 2.44/1.39  tff(c_159, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=B_50 | ~v4_pre_topc(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.44/1.39  tff(c_174, plain, (![A_49]: (k2_pre_topc(A_49, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_49) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_16, c_159])).
% 2.44/1.39  tff(c_227, plain, (![A_61]: (k2_pre_topc(A_61, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(resolution, [status(thm)], [c_206, c_174])).
% 2.44/1.39  tff(c_230, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_227])).
% 2.44/1.39  tff(c_233, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_230])).
% 2.44/1.39  tff(c_94, plain, (![A_40, B_41]: (m1_subset_1(k3_subset_1(A_40, B_41), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.44/1.39  tff(c_104, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_94])).
% 2.44/1.39  tff(c_109, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_104])).
% 2.44/1.39  tff(c_72, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.39  tff(c_74, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_72])).
% 2.44/1.39  tff(c_76, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_74])).
% 2.44/1.39  tff(c_312, plain, (![A_67, B_68]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k3_subset_1(u1_struct_0(A_67), B_68)))=k1_tops_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.44/1.39  tff(c_343, plain, (![A_67]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k1_xboole_0))=k1_tops_1(A_67, u1_struct_0(A_67)) | ~m1_subset_1(u1_struct_0(A_67), k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(superposition, [status(thm), theory('equality')], [c_76, c_312])).
% 2.44/1.39  tff(c_426, plain, (![A_71]: (k3_subset_1(u1_struct_0(A_71), k2_pre_topc(A_71, k1_xboole_0))=k1_tops_1(A_71, u1_struct_0(A_71)) | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_343])).
% 2.44/1.39  tff(c_447, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_273, c_426])).
% 2.44/1.39  tff(c_454, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_273, c_39, c_233, c_447])).
% 2.44/1.39  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_454])).
% 2.44/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.39  
% 2.44/1.39  Inference rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Ref     : 0
% 2.44/1.39  #Sup     : 93
% 2.44/1.39  #Fact    : 0
% 2.44/1.39  #Define  : 0
% 2.44/1.39  #Split   : 2
% 2.44/1.39  #Chain   : 0
% 2.44/1.39  #Close   : 0
% 2.44/1.39  
% 2.44/1.39  Ordering : KBO
% 2.44/1.39  
% 2.44/1.39  Simplification rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Subsume      : 7
% 2.44/1.39  #Demod        : 53
% 2.44/1.39  #Tautology    : 34
% 2.44/1.39  #SimpNegUnit  : 2
% 2.44/1.39  #BackRed      : 0
% 2.44/1.39  
% 2.44/1.39  #Partial instantiations: 0
% 2.44/1.39  #Strategies tried      : 1
% 2.44/1.39  
% 2.44/1.39  Timing (in seconds)
% 2.44/1.39  ----------------------
% 2.44/1.39  Preprocessing        : 0.33
% 2.44/1.39  Parsing              : 0.18
% 2.44/1.39  CNF conversion       : 0.02
% 2.44/1.39  Main loop            : 0.25
% 2.44/1.39  Inferencing          : 0.10
% 2.44/1.39  Reduction            : 0.08
% 2.44/1.39  Demodulation         : 0.06
% 2.44/1.39  BG Simplification    : 0.02
% 2.44/1.39  Subsumption          : 0.04
% 2.44/1.39  Abstraction          : 0.01
% 2.44/1.39  MUC search           : 0.00
% 2.44/1.39  Cooper               : 0.00
% 2.44/1.39  Total                : 0.62
% 2.44/1.39  Index Insertion      : 0.00
% 2.44/1.39  Index Deletion       : 0.00
% 2.44/1.39  Index Matching       : 0.00
% 2.44/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
