%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 207 expanded)
%              Number of equality atoms :   38 ( 100 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_87,axiom,(
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

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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

tff(c_40,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_subset_1(A_7,B_8,k3_subset_1(A_7,B_8)) = k2_subset_1(A_7)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,(
    ! [A_40,B_41] :
      ( k4_subset_1(A_40,B_41,k3_subset_1(A_40,B_41)) = A_40
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_105,plain,(
    ! [A_9] : k4_subset_1(A_9,k1_xboole_0,k3_subset_1(A_9,k1_xboole_0)) = A_9 ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_109,plain,(
    ! [A_9] : k4_subset_1(A_9,k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_105])).

tff(c_200,plain,(
    ! [A_58,B_59] :
      ( k4_subset_1(u1_struct_0(A_58),B_59,k3_subset_1(u1_struct_0(A_58),B_59)) = k2_struct_0(A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    ! [A_58] :
      ( k4_subset_1(u1_struct_0(A_58),k1_xboole_0,u1_struct_0(A_58)) = k2_struct_0(A_58)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_struct_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_200])).

tff(c_221,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_109,c_214])).

tff(c_226,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_22,c_221])).

tff(c_230,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_226])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_141,plain,(
    ! [B_46,A_47] :
      ( v4_pre_topc(B_46,A_47)
      | ~ v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_145,plain,(
    ! [A_47] :
      ( v4_pre_topc(k1_xboole_0,A_47)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_141])).

tff(c_152,plain,(
    ! [A_47] :
      ( v4_pre_topc(k1_xboole_0,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_145])).

tff(c_156,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = B_51
      | ~ v4_pre_topc(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_167,plain,(
    ! [A_52] :
      ( k2_pre_topc(A_52,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_16,c_156])).

tff(c_172,plain,(
    ! [A_53] :
      ( k2_pre_topc(A_53,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_152,c_167])).

tff(c_175,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_172])).

tff(c_178,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_175])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,(
    ! [A_9] : k3_subset_1(A_9,k3_subset_1(A_9,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_75,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_71])).

tff(c_273,plain,(
    ! [A_62,B_63] :
      ( k3_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,k3_subset_1(u1_struct_0(A_62),B_63))) = k1_tops_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_298,plain,(
    ! [A_62] :
      ( k3_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,k1_xboole_0)) = k1_tops_1(A_62,u1_struct_0(A_62))
      | ~ m1_subset_1(u1_struct_0(A_62),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_273])).

tff(c_374,plain,(
    ! [A_67] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k1_xboole_0)) = k1_tops_1(A_67,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_298])).

tff(c_389,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_374])).

tff(c_396,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_230,c_40,c_178,c_389])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.37  
% 2.37/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.37  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.37/1.37  
% 2.37/1.37  %Foreground sorts:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Background operators:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Foreground operators:
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.37/1.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.37/1.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.37  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.37/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.37/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.37/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.37/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.37  
% 2.69/1.39  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.69/1.39  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.69/1.39  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.69/1.39  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.69/1.39  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.69/1.39  tff(f_38, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.69/1.39  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.69/1.39  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.69/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.39  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.69/1.39  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.69/1.39  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.69/1.39  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.69/1.39  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.69/1.39  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.39  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.39  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.39  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.39  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.69/1.39  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.69/1.39  tff(c_12, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=k2_subset_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.39  tff(c_38, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.69/1.39  tff(c_40, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_38])).
% 2.69/1.39  tff(c_14, plain, (![A_7, B_8]: (k4_subset_1(A_7, B_8, k3_subset_1(A_7, B_8))=k2_subset_1(A_7) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.39  tff(c_103, plain, (![A_40, B_41]: (k4_subset_1(A_40, B_41, k3_subset_1(A_40, B_41))=A_40 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.69/1.39  tff(c_105, plain, (![A_9]: (k4_subset_1(A_9, k1_xboole_0, k3_subset_1(A_9, k1_xboole_0))=A_9)), inference(resolution, [status(thm)], [c_16, c_103])).
% 2.69/1.39  tff(c_109, plain, (![A_9]: (k4_subset_1(A_9, k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_105])).
% 2.69/1.39  tff(c_200, plain, (![A_58, B_59]: (k4_subset_1(u1_struct_0(A_58), B_59, k3_subset_1(u1_struct_0(A_58), B_59))=k2_struct_0(A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.69/1.39  tff(c_214, plain, (![A_58]: (k4_subset_1(u1_struct_0(A_58), k1_xboole_0, u1_struct_0(A_58))=k2_struct_0(A_58) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_struct_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_40, c_200])).
% 2.69/1.39  tff(c_221, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_109, c_214])).
% 2.69/1.39  tff(c_226, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_22, c_221])).
% 2.69/1.39  tff(c_230, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_226])).
% 2.69/1.39  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.69/1.39  tff(c_141, plain, (![B_46, A_47]: (v4_pre_topc(B_46, A_47) | ~v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.39  tff(c_145, plain, (![A_47]: (v4_pre_topc(k1_xboole_0, A_47) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(resolution, [status(thm)], [c_16, c_141])).
% 2.69/1.39  tff(c_152, plain, (![A_47]: (v4_pre_topc(k1_xboole_0, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_145])).
% 2.69/1.39  tff(c_156, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=B_51 | ~v4_pre_topc(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.69/1.39  tff(c_167, plain, (![A_52]: (k2_pre_topc(A_52, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_16, c_156])).
% 2.69/1.39  tff(c_172, plain, (![A_53]: (k2_pre_topc(A_53, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(resolution, [status(thm)], [c_152, c_167])).
% 2.69/1.39  tff(c_175, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_172])).
% 2.69/1.39  tff(c_178, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_175])).
% 2.69/1.39  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.39  tff(c_37, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.69/1.39  tff(c_69, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.39  tff(c_71, plain, (![A_9]: (k3_subset_1(A_9, k3_subset_1(A_9, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_69])).
% 2.69/1.39  tff(c_75, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_71])).
% 2.69/1.39  tff(c_273, plain, (![A_62, B_63]: (k3_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, k3_subset_1(u1_struct_0(A_62), B_63)))=k1_tops_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.69/1.39  tff(c_298, plain, (![A_62]: (k3_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, k1_xboole_0))=k1_tops_1(A_62, u1_struct_0(A_62)) | ~m1_subset_1(u1_struct_0(A_62), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(superposition, [status(thm), theory('equality')], [c_75, c_273])).
% 2.69/1.39  tff(c_374, plain, (![A_67]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k1_xboole_0))=k1_tops_1(A_67, u1_struct_0(A_67)) | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_298])).
% 2.69/1.39  tff(c_389, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_374])).
% 2.69/1.39  tff(c_396, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_230, c_40, c_178, c_389])).
% 2.69/1.39  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_396])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 77
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 2
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 6
% 2.69/1.39  #Demod        : 58
% 2.69/1.39  #Tautology    : 34
% 2.69/1.39  #SimpNegUnit  : 2
% 2.69/1.39  #BackRed      : 0
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.32
% 2.69/1.39  Parsing              : 0.19
% 2.69/1.39  CNF conversion       : 0.02
% 2.69/1.40  Main loop            : 0.26
% 2.69/1.40  Inferencing          : 0.10
% 2.69/1.40  Reduction            : 0.08
% 2.69/1.40  Demodulation         : 0.06
% 2.69/1.40  BG Simplification    : 0.02
% 2.69/1.40  Subsumption          : 0.04
% 2.69/1.40  Abstraction          : 0.01
% 2.69/1.40  MUC search           : 0.00
% 2.69/1.40  Cooper               : 0.00
% 2.69/1.40  Total                : 0.62
% 2.69/1.40  Index Insertion      : 0.00
% 2.69/1.40  Index Deletion       : 0.00
% 2.69/1.40  Index Matching       : 0.00
% 2.69/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
