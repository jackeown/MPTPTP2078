%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 191 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_34,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_32,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_subset_1(A_8)) = k2_subset_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_subset_1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_39,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_85,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_107,plain,(
    ! [B_47,A_48] :
      ( v4_pre_topc(B_47,A_48)
      | ~ v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_110,plain,(
    ! [B_47] :
      ( v4_pre_topc(B_47,'#skF_1')
      | ~ v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_107])).

tff(c_144,plain,(
    ! [B_51] :
      ( v4_pre_topc(B_51,'#skF_1')
      | ~ v1_xboole_0(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_110])).

tff(c_148,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_144])).

tff(c_155,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_281,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(k2_pre_topc(A_58,C_59),B_60)
      | ~ r1_tarski(C_59,B_60)
      | ~ v4_pre_topc(B_60,A_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_286,plain,(
    ! [A_58,B_60] :
      ( r1_tarski(k2_pre_topc(A_58,k1_xboole_0),B_60)
      | ~ r1_tarski(k1_xboole_0,B_60)
      | ~ v4_pre_topc(B_60,A_58)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_281])).

tff(c_296,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k2_pre_topc(A_61,k1_xboole_0),B_62)
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_286])).

tff(c_312,plain,(
    ! [A_63] :
      ( r1_tarski(k2_pre_topc(A_63,k1_xboole_0),k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_317,plain,(
    ! [A_64] :
      ( k2_pre_topc(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_312,c_6])).

tff(c_320,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_317])).

tff(c_326,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_320])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( k3_subset_1(A_45,k3_subset_1(A_45,B_46)) = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [A_9] : k3_subset_1(A_9,k3_subset_1(A_9,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_99])).

tff(c_105,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_101])).

tff(c_157,plain,(
    ! [A_52,B_53] :
      ( k3_subset_1(u1_struct_0(A_52),k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53))) = k1_tops_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_179,plain,(
    ! [B_53] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_53))) = k1_tops_1('#skF_1',B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_157])).

tff(c_201,plain,(
    ! [B_55] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_55))) = k1_tops_1('#skF_1',B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_85,c_85,c_179])).

tff(c_217,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_201])).

tff(c_225,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_217])).

tff(c_342,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_225])).

tff(c_344,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_342])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:20:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.34  
% 2.34/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.35  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.34/1.35  
% 2.34/1.35  %Foreground sorts:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Background operators:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Foreground operators:
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.34/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.34/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.35  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.34/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.34/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.34/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.34/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.35  
% 2.48/1.36  tff(f_99, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.48/1.36  tff(f_34, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.48/1.36  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.48/1.36  tff(f_44, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.48/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.36  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.48/1.36  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.48/1.36  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.48/1.36  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.48/1.36  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.48/1.36  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 2.48/1.36  tff(f_32, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.48/1.36  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.48/1.36  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.48/1.36  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.48/1.36  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.48/1.36  tff(c_8, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.36  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.36  tff(c_16, plain, (![A_8]: (k3_subset_1(A_8, k1_subset_1(A_8))=k2_subset_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.36  tff(c_38, plain, (![A_8]: (k3_subset_1(A_8, k1_subset_1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 2.48/1.36  tff(c_39, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38])).
% 2.48/1.36  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.48/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.36  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.36  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.48/1.36  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.36  tff(c_76, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.36  tff(c_81, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_26, c_76])).
% 2.48/1.36  tff(c_85, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.48/1.36  tff(c_107, plain, (![B_47, A_48]: (v4_pre_topc(B_47, A_48) | ~v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.36  tff(c_110, plain, (![B_47]: (v4_pre_topc(B_47, '#skF_1') | ~v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_107])).
% 2.48/1.36  tff(c_144, plain, (![B_51]: (v4_pre_topc(B_51, '#skF_1') | ~v1_xboole_0(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_110])).
% 2.48/1.36  tff(c_148, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_144])).
% 2.48/1.36  tff(c_155, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_148])).
% 2.48/1.36  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.48/1.36  tff(c_281, plain, (![A_58, C_59, B_60]: (r1_tarski(k2_pre_topc(A_58, C_59), B_60) | ~r1_tarski(C_59, B_60) | ~v4_pre_topc(B_60, A_58) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.36  tff(c_286, plain, (![A_58, B_60]: (r1_tarski(k2_pre_topc(A_58, k1_xboole_0), B_60) | ~r1_tarski(k1_xboole_0, B_60) | ~v4_pre_topc(B_60, A_58) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_18, c_281])).
% 2.48/1.36  tff(c_296, plain, (![A_61, B_62]: (r1_tarski(k2_pre_topc(A_61, k1_xboole_0), B_62) | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_286])).
% 2.48/1.36  tff(c_312, plain, (![A_63]: (r1_tarski(k2_pre_topc(A_63, k1_xboole_0), k1_xboole_0) | ~v4_pre_topc(k1_xboole_0, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.48/1.36  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.36  tff(c_317, plain, (![A_64]: (k2_pre_topc(A_64, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_312, c_6])).
% 2.48/1.36  tff(c_320, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_155, c_317])).
% 2.48/1.36  tff(c_326, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_320])).
% 2.48/1.36  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.36  tff(c_37, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.48/1.36  tff(c_99, plain, (![A_45, B_46]: (k3_subset_1(A_45, k3_subset_1(A_45, B_46))=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.36  tff(c_101, plain, (![A_9]: (k3_subset_1(A_9, k3_subset_1(A_9, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_99])).
% 2.48/1.36  tff(c_105, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_101])).
% 2.48/1.36  tff(c_157, plain, (![A_52, B_53]: (k3_subset_1(u1_struct_0(A_52), k2_pre_topc(A_52, k3_subset_1(u1_struct_0(A_52), B_53)))=k1_tops_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.36  tff(c_179, plain, (![B_53]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_53)))=k1_tops_1('#skF_1', B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_157])).
% 2.48/1.36  tff(c_201, plain, (![B_55]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_55)))=k1_tops_1('#skF_1', B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_85, c_85, c_179])).
% 2.48/1.36  tff(c_217, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_201])).
% 2.48/1.36  tff(c_225, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_217])).
% 2.48/1.36  tff(c_342, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_225])).
% 2.48/1.36  tff(c_344, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_342])).
% 2.48/1.36  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_344])).
% 2.48/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  Inference rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Ref     : 0
% 2.48/1.36  #Sup     : 65
% 2.48/1.36  #Fact    : 0
% 2.48/1.36  #Define  : 0
% 2.48/1.36  #Split   : 1
% 2.48/1.36  #Chain   : 0
% 2.48/1.36  #Close   : 0
% 2.48/1.36  
% 2.48/1.36  Ordering : KBO
% 2.48/1.36  
% 2.48/1.36  Simplification rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Subsume      : 2
% 2.48/1.36  #Demod        : 42
% 2.48/1.36  #Tautology    : 30
% 2.48/1.36  #SimpNegUnit  : 1
% 2.48/1.36  #BackRed      : 2
% 2.48/1.36  
% 2.48/1.36  #Partial instantiations: 0
% 2.48/1.36  #Strategies tried      : 1
% 2.48/1.36  
% 2.48/1.36  Timing (in seconds)
% 2.48/1.36  ----------------------
% 2.48/1.36  Preprocessing        : 0.32
% 2.48/1.36  Parsing              : 0.18
% 2.48/1.36  CNF conversion       : 0.02
% 2.48/1.36  Main loop            : 0.22
% 2.48/1.36  Inferencing          : 0.08
% 2.48/1.36  Reduction            : 0.07
% 2.48/1.36  Demodulation         : 0.05
% 2.48/1.36  BG Simplification    : 0.01
% 2.48/1.36  Subsumption          : 0.03
% 2.48/1.36  Abstraction          : 0.01
% 2.48/1.36  MUC search           : 0.00
% 2.48/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.57
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
