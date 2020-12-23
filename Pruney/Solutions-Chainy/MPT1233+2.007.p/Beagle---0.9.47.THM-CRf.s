%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 233 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_subset_1(A_10,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_174])).

tff(c_183,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_180])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_279,plain,(
    ! [B_70,A_71] :
      ( v4_pre_topc(B_70,A_71)
      | ~ v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_290,plain,(
    ! [A_71] :
      ( v4_pre_topc(k1_xboole_0,A_71)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_20,c_279])).

tff(c_297,plain,(
    ! [A_72] :
      ( v4_pre_topc(k1_xboole_0,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_32,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_222,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,B_64) = B_64
      | ~ v4_pre_topc(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_229,plain,(
    ! [B_64] :
      ( k2_pre_topc('#skF_1',B_64) = B_64
      | ~ v4_pre_topc(B_64,'#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_222])).

tff(c_267,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',B_69) = B_69
      | ~ v4_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_229])).

tff(c_277,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_267])).

tff(c_278,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_300,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_297,c_278])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_300])).

tff(c_308,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_117,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_117])).

tff(c_184,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_123])).

tff(c_489,plain,(
    ! [A_90,B_91] :
      ( k3_subset_1(u1_struct_0(A_90),k2_pre_topc(A_90,k3_subset_1(u1_struct_0(A_90),B_91))) = k1_tops_1(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_522,plain,(
    ! [B_91] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_91))) = k1_tops_1('#skF_1',B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_489])).

tff(c_633,plain,(
    ! [B_99] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_99))) = k1_tops_1('#skF_1',B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_73,c_73,c_522])).

tff(c_655,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_633])).

tff(c_666,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_308,c_655])).

tff(c_667,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_666])).

tff(c_672,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_667])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:58:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.46  
% 2.67/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.46  %$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 3.01/1.46  
% 3.01/1.46  %Foreground sorts:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Background operators:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Foreground operators:
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.01/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.01/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.01/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.01/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.01/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.01/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.01/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.46  
% 3.02/1.48  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.02/1.48  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.48  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.02/1.48  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.02/1.48  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.48  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.02/1.48  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.02/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.02/1.48  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.02/1.48  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.02/1.48  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.02/1.48  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.02/1.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.02/1.48  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 3.02/1.48  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.48  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.48  tff(c_40, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.02/1.48  tff(c_10, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.48  tff(c_55, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.48  tff(c_59, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(resolution, [status(thm)], [c_10, c_55])).
% 3.02/1.48  tff(c_20, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.02/1.48  tff(c_174, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.02/1.48  tff(c_180, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_174])).
% 3.02/1.48  tff(c_183, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_180])).
% 3.02/1.48  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.02/1.48  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.02/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.02/1.48  tff(c_279, plain, (![B_70, A_71]: (v4_pre_topc(B_70, A_71) | ~v1_xboole_0(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.48  tff(c_290, plain, (![A_71]: (v4_pre_topc(k1_xboole_0, A_71) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(resolution, [status(thm)], [c_20, c_279])).
% 3.02/1.48  tff(c_297, plain, (![A_72]: (v4_pre_topc(k1_xboole_0, A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_290])).
% 3.02/1.48  tff(c_32, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.02/1.48  tff(c_50, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.02/1.48  tff(c_69, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_32, c_50])).
% 3.02/1.48  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.02/1.48  tff(c_222, plain, (![A_63, B_64]: (k2_pre_topc(A_63, B_64)=B_64 | ~v4_pre_topc(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.02/1.48  tff(c_229, plain, (![B_64]: (k2_pre_topc('#skF_1', B_64)=B_64 | ~v4_pre_topc(B_64, '#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_222])).
% 3.02/1.48  tff(c_267, plain, (![B_69]: (k2_pre_topc('#skF_1', B_69)=B_69 | ~v4_pre_topc(B_69, '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_229])).
% 3.02/1.48  tff(c_277, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_20, c_267])).
% 3.02/1.48  tff(c_278, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_277])).
% 3.02/1.48  tff(c_300, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_297, c_278])).
% 3.02/1.48  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_300])).
% 3.02/1.48  tff(c_308, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_277])).
% 3.02/1.48  tff(c_117, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.02/1.48  tff(c_123, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_117])).
% 3.02/1.48  tff(c_184, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_123])).
% 3.02/1.48  tff(c_489, plain, (![A_90, B_91]: (k3_subset_1(u1_struct_0(A_90), k2_pre_topc(A_90, k3_subset_1(u1_struct_0(A_90), B_91)))=k1_tops_1(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.02/1.48  tff(c_522, plain, (![B_91]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_91)))=k1_tops_1('#skF_1', B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_489])).
% 3.02/1.48  tff(c_633, plain, (![B_99]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_99)))=k1_tops_1('#skF_1', B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_73, c_73, c_522])).
% 3.02/1.48  tff(c_655, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_184, c_633])).
% 3.02/1.48  tff(c_666, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_308, c_655])).
% 3.02/1.48  tff(c_667, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_666])).
% 3.02/1.48  tff(c_672, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_667])).
% 3.02/1.48  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_672])).
% 3.02/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  Inference rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Ref     : 0
% 3.02/1.48  #Sup     : 126
% 3.02/1.48  #Fact    : 0
% 3.02/1.48  #Define  : 0
% 3.02/1.48  #Split   : 2
% 3.02/1.48  #Chain   : 0
% 3.02/1.48  #Close   : 0
% 3.02/1.48  
% 3.02/1.48  Ordering : KBO
% 3.02/1.48  
% 3.02/1.48  Simplification rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Subsume      : 11
% 3.02/1.48  #Demod        : 90
% 3.02/1.48  #Tautology    : 52
% 3.02/1.48  #SimpNegUnit  : 6
% 3.02/1.48  #BackRed      : 1
% 3.02/1.48  
% 3.02/1.48  #Partial instantiations: 0
% 3.02/1.48  #Strategies tried      : 1
% 3.02/1.48  
% 3.02/1.48  Timing (in seconds)
% 3.02/1.48  ----------------------
% 3.02/1.48  Preprocessing        : 0.34
% 3.02/1.48  Parsing              : 0.18
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.31
% 3.02/1.48  Inferencing          : 0.12
% 3.02/1.48  Reduction            : 0.10
% 3.02/1.48  Demodulation         : 0.07
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.05
% 3.02/1.48  Abstraction          : 0.02
% 3.02/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.69
% 3.02/1.48  Index Insertion      : 0.00
% 3.02/1.48  Index Deletion       : 0.00
% 3.02/1.48  Index Matching       : 0.00
% 3.02/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
