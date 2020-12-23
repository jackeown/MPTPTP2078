%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 224 expanded)
%              Number of leaves         :   36 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 342 expanded)
%              Number of equality atoms :   38 ( 141 expanded)
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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_92,axiom,(
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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_34,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_subset_1(A_8)) = k2_subset_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_subset_1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_41,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_struct_0(A_17))
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_71,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | B_32 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_88,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_struct_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_93,plain,(
    ! [A_36] :
      ( k1_struct_0(A_36) = k1_xboole_0
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_97,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_26,plain,(
    ! [A_18] :
      ( k3_subset_1(u1_struct_0(A_18),k1_struct_0(A_18)) = k2_struct_0(A_18)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_26])).

tff(c_116,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_110])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_122,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_127,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_204,plain,(
    ! [B_52,A_53] :
      ( v4_pre_topc(B_52,A_53)
      | ~ v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_207,plain,(
    ! [B_52] :
      ( v4_pre_topc(B_52,'#skF_1')
      | ~ v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_204])).

tff(c_225,plain,(
    ! [B_59] :
      ( v4_pre_topc(B_59,'#skF_1')
      | ~ v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_207])).

tff(c_229,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_225])).

tff(c_236,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_229])).

tff(c_238,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = B_61
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_241,plain,(
    ! [B_61] :
      ( k2_pre_topc('#skF_1',B_61) = B_61
      | ~ v4_pre_topc(B_61,'#skF_1')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_238])).

tff(c_266,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',B_63) = B_63
      | ~ v4_pre_topc(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_270,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_266])).

tff(c_277,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_270])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_171,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [A_9] : k3_subset_1(A_9,k3_subset_1(A_9,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_177,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_173])).

tff(c_357,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(u1_struct_0(A_72),k2_pre_topc(A_72,k3_subset_1(u1_struct_0(A_72),B_73))) = k1_tops_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_373,plain,(
    ! [A_72] :
      ( k3_subset_1(u1_struct_0(A_72),k2_pre_topc(A_72,k1_xboole_0)) = k1_tops_1(A_72,u1_struct_0(A_72))
      | ~ m1_subset_1(u1_struct_0(A_72),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_357])).

tff(c_433,plain,(
    ! [A_76] :
      ( k3_subset_1(u1_struct_0(A_76),k2_pre_topc(A_76,k1_xboole_0)) = k1_tops_1(A_76,u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_373])).

tff(c_445,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_433])).

tff(c_452,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_127,c_127,c_41,c_445])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.35/1.30  
% 2.35/1.30  %Foreground sorts:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Background operators:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Foreground operators:
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.35/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.35/1.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.35/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.35/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.35/1.30  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.35/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.35/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.35/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.35/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.35/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.30  
% 2.35/1.31  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.35/1.31  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.35/1.31  tff(f_36, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.35/1.31  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.35/1.31  tff(f_46, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.35/1.31  tff(f_73, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.35/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.35/1.31  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.35/1.31  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.35/1.31  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.35/1.31  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.35/1.31  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.35/1.31  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.35/1.31  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.35/1.31  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.35/1.31  tff(c_34, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.35/1.31  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.35/1.31  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.35/1.31  tff(c_6, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.35/1.31  tff(c_8, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.31  tff(c_14, plain, (![A_8]: (k3_subset_1(A_8, k1_subset_1(A_8))=k2_subset_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.31  tff(c_40, plain, (![A_8]: (k3_subset_1(A_8, k1_subset_1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.35/1.31  tff(c_41, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40])).
% 2.35/1.31  tff(c_24, plain, (![A_17]: (v1_xboole_0(k1_struct_0(A_17)) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.35/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.35/1.31  tff(c_71, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | B_32=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.35/1.31  tff(c_78, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.35/1.31  tff(c_88, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_struct_0(A_35))), inference(resolution, [status(thm)], [c_24, c_78])).
% 2.35/1.31  tff(c_93, plain, (![A_36]: (k1_struct_0(A_36)=k1_xboole_0 | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_22, c_88])).
% 2.35/1.31  tff(c_97, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_93])).
% 2.35/1.31  tff(c_26, plain, (![A_18]: (k3_subset_1(u1_struct_0(A_18), k1_struct_0(A_18))=k2_struct_0(A_18) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.35/1.31  tff(c_110, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_26])).
% 2.35/1.31  tff(c_116, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_110])).
% 2.35/1.31  tff(c_119, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_116])).
% 2.35/1.31  tff(c_122, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_119])).
% 2.35/1.31  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_122])).
% 2.35/1.31  tff(c_127, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 2.35/1.31  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.35/1.31  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.35/1.31  tff(c_204, plain, (![B_52, A_53]: (v4_pre_topc(B_52, A_53) | ~v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.35/1.31  tff(c_207, plain, (![B_52]: (v4_pre_topc(B_52, '#skF_1') | ~v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_204])).
% 2.35/1.31  tff(c_225, plain, (![B_59]: (v4_pre_topc(B_59, '#skF_1') | ~v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_207])).
% 2.35/1.31  tff(c_229, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_225])).
% 2.35/1.31  tff(c_236, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_229])).
% 2.35/1.31  tff(c_238, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=B_61 | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.35/1.31  tff(c_241, plain, (![B_61]: (k2_pre_topc('#skF_1', B_61)=B_61 | ~v4_pre_topc(B_61, '#skF_1') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_238])).
% 2.35/1.31  tff(c_266, plain, (![B_63]: (k2_pre_topc('#skF_1', B_63)=B_63 | ~v4_pre_topc(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_241])).
% 2.35/1.31  tff(c_270, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_16, c_266])).
% 2.35/1.31  tff(c_277, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_236, c_270])).
% 2.35/1.31  tff(c_10, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.31  tff(c_39, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.35/1.31  tff(c_171, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.31  tff(c_173, plain, (![A_9]: (k3_subset_1(A_9, k3_subset_1(A_9, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_171])).
% 2.35/1.31  tff(c_177, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_173])).
% 2.35/1.31  tff(c_357, plain, (![A_72, B_73]: (k3_subset_1(u1_struct_0(A_72), k2_pre_topc(A_72, k3_subset_1(u1_struct_0(A_72), B_73)))=k1_tops_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.35/1.31  tff(c_373, plain, (![A_72]: (k3_subset_1(u1_struct_0(A_72), k2_pre_topc(A_72, k1_xboole_0))=k1_tops_1(A_72, u1_struct_0(A_72)) | ~m1_subset_1(u1_struct_0(A_72), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(superposition, [status(thm), theory('equality')], [c_177, c_357])).
% 2.35/1.31  tff(c_433, plain, (![A_76]: (k3_subset_1(u1_struct_0(A_76), k2_pre_topc(A_76, k1_xboole_0))=k1_tops_1(A_76, u1_struct_0(A_76)) | ~l1_pre_topc(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_373])).
% 2.35/1.31  tff(c_445, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_277, c_433])).
% 2.35/1.31  tff(c_452, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_127, c_127, c_41, c_445])).
% 2.35/1.31  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_452])).
% 2.35/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  Inference rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Ref     : 0
% 2.35/1.31  #Sup     : 87
% 2.35/1.31  #Fact    : 0
% 2.35/1.31  #Define  : 0
% 2.35/1.31  #Split   : 3
% 2.35/1.31  #Chain   : 0
% 2.35/1.31  #Close   : 0
% 2.35/1.31  
% 2.35/1.31  Ordering : KBO
% 2.35/1.31  
% 2.35/1.31  Simplification rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Subsume      : 9
% 2.35/1.31  #Demod        : 74
% 2.35/1.31  #Tautology    : 38
% 2.35/1.31  #SimpNegUnit  : 5
% 2.35/1.31  #BackRed      : 0
% 2.35/1.31  
% 2.35/1.31  #Partial instantiations: 0
% 2.35/1.31  #Strategies tried      : 1
% 2.35/1.31  
% 2.35/1.31  Timing (in seconds)
% 2.35/1.31  ----------------------
% 2.35/1.32  Preprocessing        : 0.29
% 2.35/1.32  Parsing              : 0.17
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.25
% 2.35/1.32  Inferencing          : 0.10
% 2.35/1.32  Reduction            : 0.08
% 2.35/1.32  Demodulation         : 0.05
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.04
% 2.35/1.32  Abstraction          : 0.01
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.58
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
