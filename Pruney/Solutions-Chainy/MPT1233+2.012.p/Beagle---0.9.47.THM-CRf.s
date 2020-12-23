%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 185 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 324 expanded)
%              Number of equality atoms :   34 ( 102 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

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
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
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

tff(f_34,axiom,(
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

tff(c_30,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_35,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    ! [A_26] :
      ( k1_struct_0(A_26) = k1_xboole_0
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    ! [A_27] :
      ( k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_57,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_62,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_76,plain,(
    ! [A_30] :
      ( k3_subset_1(u1_struct_0(A_30),k1_struct_0(A_30)) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_76])).

tff(c_91,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_85])).

tff(c_102,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_106])).

tff(c_111,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_203,plain,(
    ! [B_46,A_47] :
      ( v4_pre_topc(B_46,A_47)
      | ~ v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_210,plain,(
    ! [A_47] :
      ( v4_pre_topc(k1_xboole_0,A_47)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_10,c_203])).

tff(c_221,plain,(
    ! [A_48] :
      ( v4_pre_topc(k1_xboole_0,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_136,plain,(
    ! [A_40,B_41] :
      ( k2_pre_topc(A_40,B_41) = B_41
      | ~ v4_pre_topc(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,(
    ! [B_41] :
      ( k2_pre_topc('#skF_1',B_41) = B_41
      | ~ v4_pre_topc(B_41,'#skF_1')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_136])).

tff(c_189,plain,(
    ! [B_44] :
      ( k2_pre_topc('#skF_1',B_44) = B_44
      | ~ v4_pre_topc(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_198,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_200,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_227,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_221,c_200])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_227])).

tff(c_233,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_129,plain,(
    ! [A_38,B_39] :
      ( k3_subset_1(A_38,k3_subset_1(A_38,B_39)) = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152,plain,(
    ! [A_42] : k3_subset_1(A_42,k3_subset_1(A_42,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_159,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_152])).

tff(c_357,plain,(
    ! [A_62,B_63] :
      ( k3_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,k3_subset_1(u1_struct_0(A_62),B_63))) = k1_tops_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_386,plain,(
    ! [B_63] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_63))) = k1_tops_1('#skF_1',B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_357])).

tff(c_407,plain,(
    ! [B_65] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_65))) = k1_tops_1('#skF_1',B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_71,c_71,c_386])).

tff(c_425,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_407])).

tff(c_440,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_111,c_233,c_425])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.31/1.33  
% 2.31/1.33  %Foreground sorts:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Background operators:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Foreground operators:
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.31/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.31/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.31/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.33  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.31/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.31/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.31/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.31/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.31/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.33  
% 2.62/1.35  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.62/1.35  tff(f_28, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.62/1.35  tff(f_30, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.62/1.35  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.62/1.35  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.62/1.35  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.62/1.35  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.62/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.35  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.62/1.35  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.62/1.35  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.62/1.35  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.62/1.35  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.62/1.35  tff(c_30, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.62/1.35  tff(c_4, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.62/1.35  tff(c_6, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.62/1.35  tff(c_35, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.62/1.35  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.62/1.35  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.35  tff(c_48, plain, (![A_26]: (k1_struct_0(A_26)=k1_xboole_0 | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.35  tff(c_53, plain, (![A_27]: (k1_struct_0(A_27)=k1_xboole_0 | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_20, c_48])).
% 2.62/1.35  tff(c_57, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.62/1.35  tff(c_62, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.35  tff(c_67, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_20, c_62])).
% 2.62/1.35  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_67])).
% 2.62/1.35  tff(c_76, plain, (![A_30]: (k3_subset_1(u1_struct_0(A_30), k1_struct_0(A_30))=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.35  tff(c_85, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71, c_76])).
% 2.62/1.35  tff(c_91, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_85])).
% 2.62/1.35  tff(c_102, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_91])).
% 2.62/1.35  tff(c_106, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_102])).
% 2.62/1.35  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_106])).
% 2.62/1.35  tff(c_111, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_91])).
% 2.62/1.35  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.62/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.62/1.35  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.35  tff(c_203, plain, (![B_46, A_47]: (v4_pre_topc(B_46, A_47) | ~v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.35  tff(c_210, plain, (![A_47]: (v4_pre_topc(k1_xboole_0, A_47) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(resolution, [status(thm)], [c_10, c_203])).
% 2.62/1.35  tff(c_221, plain, (![A_48]: (v4_pre_topc(k1_xboole_0, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210])).
% 2.62/1.35  tff(c_136, plain, (![A_40, B_41]: (k2_pre_topc(A_40, B_41)=B_41 | ~v4_pre_topc(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.62/1.35  tff(c_139, plain, (![B_41]: (k2_pre_topc('#skF_1', B_41)=B_41 | ~v4_pre_topc(B_41, '#skF_1') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_136])).
% 2.62/1.35  tff(c_189, plain, (![B_44]: (k2_pre_topc('#skF_1', B_44)=B_44 | ~v4_pre_topc(B_44, '#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139])).
% 2.62/1.35  tff(c_198, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_10, c_189])).
% 2.62/1.35  tff(c_200, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_198])).
% 2.62/1.35  tff(c_227, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_221, c_200])).
% 2.62/1.35  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_227])).
% 2.62/1.35  tff(c_233, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_198])).
% 2.62/1.35  tff(c_129, plain, (![A_38, B_39]: (k3_subset_1(A_38, k3_subset_1(A_38, B_39))=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.35  tff(c_152, plain, (![A_42]: (k3_subset_1(A_42, k3_subset_1(A_42, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_129])).
% 2.62/1.35  tff(c_159, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_152])).
% 2.62/1.35  tff(c_357, plain, (![A_62, B_63]: (k3_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, k3_subset_1(u1_struct_0(A_62), B_63)))=k1_tops_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.62/1.35  tff(c_386, plain, (![B_63]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_63)))=k1_tops_1('#skF_1', B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_357])).
% 2.62/1.35  tff(c_407, plain, (![B_65]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_65)))=k1_tops_1('#skF_1', B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_71, c_71, c_386])).
% 2.62/1.35  tff(c_425, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_159, c_407])).
% 2.62/1.35  tff(c_440, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_111, c_233, c_425])).
% 2.62/1.35  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_440])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 86
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 5
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 5
% 2.62/1.35  #Demod        : 64
% 2.62/1.35  #Tautology    : 36
% 2.62/1.35  #SimpNegUnit  : 6
% 2.62/1.35  #BackRed      : 0
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.35  Preprocessing        : 0.30
% 2.62/1.35  Parsing              : 0.16
% 2.62/1.35  CNF conversion       : 0.02
% 2.62/1.35  Main loop            : 0.25
% 2.62/1.35  Inferencing          : 0.10
% 2.62/1.35  Reduction            : 0.08
% 2.62/1.35  Demodulation         : 0.05
% 2.62/1.35  BG Simplification    : 0.01
% 2.62/1.35  Subsumption          : 0.04
% 2.62/1.35  Abstraction          : 0.01
% 2.62/1.35  MUC search           : 0.00
% 2.62/1.35  Cooper               : 0.00
% 2.62/1.35  Total                : 0.58
% 2.62/1.35  Index Insertion      : 0.00
% 2.62/1.35  Index Deletion       : 0.00
% 2.62/1.35  Index Matching       : 0.00
% 2.62/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
