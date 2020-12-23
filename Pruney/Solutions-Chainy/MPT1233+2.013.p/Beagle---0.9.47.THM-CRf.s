%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 204 expanded)
%              Number of leaves         :   35 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 308 expanded)
%              Number of equality atoms :   36 ( 138 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_84,axiom,(
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

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = k2_subset_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_39,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_29] :
      ( k1_struct_0(A_29) = k1_xboole_0
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_73,plain,(
    ! [A_30] :
      ( k1_struct_0(A_30) = k1_xboole_0
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_77,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_82,plain,(
    ! [A_31] :
      ( k3_subset_1(u1_struct_0(A_31),k1_struct_0(A_31)) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_82])).

tff(c_94,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_91])).

tff(c_95,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_110,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_197,plain,(
    ! [B_50,A_51] :
      ( v4_pre_topc(B_50,A_51)
      | ~ v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_208,plain,(
    ! [A_51] :
      ( v4_pre_topc(k1_xboole_0,A_51)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_231,plain,(
    ! [A_54] :
      ( v4_pre_topc(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_161,plain,(
    ! [A_45,B_46] :
      ( k2_pre_topc(A_45,B_46) = B_46
      | ~ v4_pre_topc(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_164,plain,(
    ! [B_46] :
      ( k2_pre_topc('#skF_1',B_46) = B_46
      | ~ v4_pre_topc(B_46,'#skF_1')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_161])).

tff(c_185,plain,(
    ! [B_49] :
      ( k2_pre_topc('#skF_1',B_49) = B_49
      | ~ v4_pre_topc(B_49,'#skF_1')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_164])).

tff(c_195,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_196,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_234,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_231,c_196])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_234])).

tff(c_242,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_135,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_139,plain,(
    ! [A_7] : k3_subset_1(A_7,k3_subset_1(A_7,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_142,plain,(
    ! [A_7] : k3_subset_1(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_139])).

tff(c_359,plain,(
    ! [A_66,B_67] :
      ( k3_subset_1(u1_struct_0(A_66),k2_pre_topc(A_66,k3_subset_1(u1_struct_0(A_66),B_67))) = k1_tops_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_375,plain,(
    ! [A_66] :
      ( k3_subset_1(u1_struct_0(A_66),k2_pre_topc(A_66,k1_xboole_0)) = k1_tops_1(A_66,u1_struct_0(A_66))
      | ~ m1_subset_1(u1_struct_0(A_66),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_359])).

tff(c_435,plain,(
    ! [A_70] :
      ( k3_subset_1(u1_struct_0(A_70),k2_pre_topc(A_70,k1_xboole_0)) = k1_tops_1(A_70,u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_375])).

tff(c_447,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_435])).

tff(c_454,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_39,c_110,c_110,c_447])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:15:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.17/1.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.17/1.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.17/1.31  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.17/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.17/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.17/1.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.17/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.58/1.33  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.58/1.33  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.58/1.33  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.58/1.33  tff(f_38, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.58/1.33  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.58/1.33  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.58/1.33  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.58/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.33  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.58/1.33  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.58/1.33  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.58/1.33  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.58/1.33  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.58/1.33  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.58/1.33  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.58/1.33  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.58/1.33  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.58/1.33  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.58/1.33  tff(c_12, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=k2_subset_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.33  tff(c_38, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.58/1.33  tff(c_39, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_38])).
% 2.58/1.33  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.33  tff(c_68, plain, (![A_29]: (k1_struct_0(A_29)=k1_xboole_0 | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.33  tff(c_73, plain, (![A_30]: (k1_struct_0(A_30)=k1_xboole_0 | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.58/1.33  tff(c_77, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.58/1.33  tff(c_82, plain, (![A_31]: (k3_subset_1(u1_struct_0(A_31), k1_struct_0(A_31))=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.58/1.33  tff(c_91, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_77, c_82])).
% 2.58/1.33  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_91])).
% 2.58/1.33  tff(c_95, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_94])).
% 2.58/1.33  tff(c_105, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_95])).
% 2.58/1.33  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 2.58/1.33  tff(c_110, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_94])).
% 2.58/1.33  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.58/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.33  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.33  tff(c_197, plain, (![B_50, A_51]: (v4_pre_topc(B_50, A_51) | ~v1_xboole_0(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.33  tff(c_208, plain, (![A_51]: (v4_pre_topc(k1_xboole_0, A_51) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(resolution, [status(thm)], [c_14, c_197])).
% 2.58/1.33  tff(c_231, plain, (![A_54]: (v4_pre_topc(k1_xboole_0, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_208])).
% 2.58/1.33  tff(c_161, plain, (![A_45, B_46]: (k2_pre_topc(A_45, B_46)=B_46 | ~v4_pre_topc(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.33  tff(c_164, plain, (![B_46]: (k2_pre_topc('#skF_1', B_46)=B_46 | ~v4_pre_topc(B_46, '#skF_1') | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_161])).
% 2.58/1.33  tff(c_185, plain, (![B_49]: (k2_pre_topc('#skF_1', B_49)=B_49 | ~v4_pre_topc(B_49, '#skF_1') | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_164])).
% 2.58/1.33  tff(c_195, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_14, c_185])).
% 2.58/1.33  tff(c_196, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_195])).
% 2.58/1.33  tff(c_234, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_231, c_196])).
% 2.58/1.33  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_234])).
% 2.58/1.33  tff(c_242, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_195])).
% 2.58/1.33  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.33  tff(c_37, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.58/1.33  tff(c_135, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.58/1.33  tff(c_139, plain, (![A_7]: (k3_subset_1(A_7, k3_subset_1(A_7, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_135])).
% 2.58/1.33  tff(c_142, plain, (![A_7]: (k3_subset_1(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_139])).
% 2.58/1.33  tff(c_359, plain, (![A_66, B_67]: (k3_subset_1(u1_struct_0(A_66), k2_pre_topc(A_66, k3_subset_1(u1_struct_0(A_66), B_67)))=k1_tops_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.33  tff(c_375, plain, (![A_66]: (k3_subset_1(u1_struct_0(A_66), k2_pre_topc(A_66, k1_xboole_0))=k1_tops_1(A_66, u1_struct_0(A_66)) | ~m1_subset_1(u1_struct_0(A_66), k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_142, c_359])).
% 2.58/1.33  tff(c_435, plain, (![A_70]: (k3_subset_1(u1_struct_0(A_70), k2_pre_topc(A_70, k1_xboole_0))=k1_tops_1(A_70, u1_struct_0(A_70)) | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_375])).
% 2.58/1.33  tff(c_447, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_242, c_435])).
% 2.58/1.33  tff(c_454, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_39, c_110, c_110, c_447])).
% 2.58/1.33  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_454])).
% 2.58/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  Inference rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Ref     : 0
% 2.58/1.33  #Sup     : 85
% 2.58/1.33  #Fact    : 0
% 2.58/1.33  #Define  : 0
% 2.58/1.33  #Split   : 3
% 2.58/1.33  #Chain   : 0
% 2.58/1.33  #Close   : 0
% 2.58/1.33  
% 2.58/1.33  Ordering : KBO
% 2.58/1.33  
% 2.58/1.33  Simplification rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Subsume      : 6
% 2.58/1.33  #Demod        : 78
% 2.58/1.33  #Tautology    : 37
% 2.58/1.33  #SimpNegUnit  : 6
% 2.58/1.33  #BackRed      : 0
% 2.58/1.33  
% 2.58/1.33  #Partial instantiations: 0
% 2.58/1.33  #Strategies tried      : 1
% 2.58/1.33  
% 2.58/1.33  Timing (in seconds)
% 2.58/1.33  ----------------------
% 2.58/1.33  Preprocessing        : 0.29
% 2.58/1.33  Parsing              : 0.17
% 2.58/1.33  CNF conversion       : 0.02
% 2.58/1.33  Main loop            : 0.25
% 2.58/1.33  Inferencing          : 0.10
% 2.58/1.33  Reduction            : 0.08
% 2.58/1.33  Demodulation         : 0.06
% 2.58/1.33  BG Simplification    : 0.01
% 2.58/1.33  Subsumption          : 0.04
% 2.58/1.33  Abstraction          : 0.01
% 2.58/1.33  MUC search           : 0.00
% 2.58/1.33  Cooper               : 0.00
% 2.58/1.33  Total                : 0.58
% 2.58/1.33  Index Insertion      : 0.00
% 2.58/1.33  Index Deletion       : 0.00
% 2.58/1.33  Index Matching       : 0.00
% 2.58/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
