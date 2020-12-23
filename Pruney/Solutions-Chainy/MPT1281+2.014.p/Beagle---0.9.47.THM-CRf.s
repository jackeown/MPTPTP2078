%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 146 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   95 ( 327 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_62,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_430,plain,(
    ! [A_86,B_87] :
      ( k2_pre_topc(A_86,k1_tops_1(A_86,B_87)) = B_87
      | ~ v5_tops_1(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_436,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_430])).

tff(c_441,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_436])).

tff(c_22,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_442,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_22])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_515,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k2_tops_1(A_93,k2_pre_topc(A_93,B_94)),k2_tops_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_522,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_515])).

tff(c_526,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_522])).

tff(c_967,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_970,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_967])).

tff(c_974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_970])).

tff(c_975,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_976,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_18,plain,(
    ! [A_18,B_20] :
      ( k4_subset_1(u1_struct_0(A_18),B_20,k2_tops_1(A_18,B_20)) = k2_pre_topc(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_981,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_976,c_18])).

tff(c_995,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_441,c_981])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k2_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_210,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_subset_1(A_60,B_61,C_62) = k2_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1910,plain,(
    ! [A_204,B_205,B_206] :
      ( k4_subset_1(u1_struct_0(A_204),B_205,k2_tops_1(A_204,B_206)) = k2_xboole_0(B_205,k2_tops_1(A_204,B_206))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_1922,plain,(
    ! [A_14,B_15,B_206] :
      ( k4_subset_1(u1_struct_0(A_14),k1_tops_1(A_14,B_15),k2_tops_1(A_14,B_206)) = k2_xboole_0(k1_tops_1(A_14,B_15),k2_tops_1(A_14,B_206))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_1910])).

tff(c_3579,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_1922])).

tff(c_3592,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_976,c_3579])).

tff(c_30,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_79,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_31,B_27,A_28] :
      ( r1_tarski(A_31,k2_xboole_0(B_27,A_28))
      | ~ r1_tarski(A_31,A_28) ) ),
    inference(resolution,[status(thm)],[c_45,c_79])).

tff(c_4458,plain,(
    ! [A_331] :
      ( r1_tarski(A_331,'#skF_2')
      | ~ r1_tarski(A_331,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3592,c_84])).

tff(c_4471,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_975,c_4458])).

tff(c_4484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_4471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.25  
% 6.28/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.25  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.28/2.25  
% 6.28/2.25  %Foreground sorts:
% 6.28/2.25  
% 6.28/2.25  
% 6.28/2.25  %Background operators:
% 6.28/2.25  
% 6.28/2.25  
% 6.28/2.25  %Foreground operators:
% 6.28/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.28/2.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.28/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.25  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.28/2.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.28/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.28/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.28/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.25  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 6.28/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.28/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.28/2.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.28/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.28/2.25  
% 6.28/2.27  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 6.28/2.27  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 6.28/2.27  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.28/2.27  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 6.28/2.27  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.28/2.27  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.28/2.27  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.28/2.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.28/2.27  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.28/2.27  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.28/2.27  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.28/2.27  tff(c_24, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.28/2.27  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.28/2.27  tff(c_430, plain, (![A_86, B_87]: (k2_pre_topc(A_86, k1_tops_1(A_86, B_87))=B_87 | ~v5_tops_1(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.28/2.27  tff(c_436, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_430])).
% 6.28/2.27  tff(c_441, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_436])).
% 6.28/2.27  tff(c_22, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.28/2.27  tff(c_442, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_22])).
% 6.28/2.27  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(k1_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.28/2.27  tff(c_515, plain, (![A_93, B_94]: (r1_tarski(k2_tops_1(A_93, k2_pre_topc(A_93, B_94)), k2_tops_1(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.28/2.27  tff(c_522, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_441, c_515])).
% 6.28/2.27  tff(c_526, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_522])).
% 6.28/2.27  tff(c_967, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_526])).
% 6.28/2.27  tff(c_970, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_967])).
% 6.28/2.27  tff(c_974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_970])).
% 6.28/2.27  tff(c_975, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_526])).
% 6.28/2.27  tff(c_976, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_526])).
% 6.28/2.27  tff(c_18, plain, (![A_18, B_20]: (k4_subset_1(u1_struct_0(A_18), B_20, k2_tops_1(A_18, B_20))=k2_pre_topc(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.28/2.27  tff(c_981, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_976, c_18])).
% 6.28/2.27  tff(c_995, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_441, c_981])).
% 6.28/2.27  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k2_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.28/2.27  tff(c_210, plain, (![A_60, B_61, C_62]: (k4_subset_1(A_60, B_61, C_62)=k2_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.28/2.27  tff(c_1910, plain, (![A_204, B_205, B_206]: (k4_subset_1(u1_struct_0(A_204), B_205, k2_tops_1(A_204, B_206))=k2_xboole_0(B_205, k2_tops_1(A_204, B_206)) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(resolution, [status(thm)], [c_16, c_210])).
% 6.28/2.27  tff(c_1922, plain, (![A_14, B_15, B_206]: (k4_subset_1(u1_struct_0(A_14), k1_tops_1(A_14, B_15), k2_tops_1(A_14, B_206))=k2_xboole_0(k1_tops_1(A_14, B_15), k2_tops_1(A_14, B_206)) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_14, c_1910])).
% 6.28/2.27  tff(c_3579, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_995, c_1922])).
% 6.28/2.27  tff(c_3592, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_976, c_3579])).
% 6.28/2.27  tff(c_30, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.27  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.28/2.27  tff(c_45, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6])).
% 6.28/2.27  tff(c_79, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.28/2.27  tff(c_84, plain, (![A_31, B_27, A_28]: (r1_tarski(A_31, k2_xboole_0(B_27, A_28)) | ~r1_tarski(A_31, A_28))), inference(resolution, [status(thm)], [c_45, c_79])).
% 6.28/2.27  tff(c_4458, plain, (![A_331]: (r1_tarski(A_331, '#skF_2') | ~r1_tarski(A_331, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_3592, c_84])).
% 6.28/2.27  tff(c_4471, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_975, c_4458])).
% 6.28/2.27  tff(c_4484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_4471])).
% 6.28/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.27  
% 6.28/2.27  Inference rules
% 6.28/2.27  ----------------------
% 6.28/2.27  #Ref     : 0
% 6.28/2.27  #Sup     : 1129
% 6.28/2.27  #Fact    : 0
% 6.28/2.27  #Define  : 0
% 6.28/2.27  #Split   : 4
% 6.28/2.27  #Chain   : 0
% 6.28/2.27  #Close   : 0
% 6.28/2.27  
% 6.28/2.27  Ordering : KBO
% 6.28/2.27  
% 6.28/2.27  Simplification rules
% 6.28/2.27  ----------------------
% 6.28/2.27  #Subsume      : 33
% 6.28/2.27  #Demod        : 376
% 6.28/2.27  #Tautology    : 369
% 6.28/2.27  #SimpNegUnit  : 3
% 6.28/2.27  #BackRed      : 2
% 6.28/2.27  
% 6.28/2.27  #Partial instantiations: 0
% 6.28/2.27  #Strategies tried      : 1
% 6.28/2.27  
% 6.28/2.27  Timing (in seconds)
% 6.28/2.27  ----------------------
% 6.28/2.27  Preprocessing        : 0.31
% 6.28/2.27  Parsing              : 0.17
% 6.28/2.27  CNF conversion       : 0.02
% 6.28/2.27  Main loop            : 1.18
% 6.28/2.27  Inferencing          : 0.29
% 6.28/2.27  Reduction            : 0.53
% 6.28/2.27  Demodulation         : 0.45
% 6.28/2.27  BG Simplification    : 0.04
% 6.28/2.27  Subsumption          : 0.24
% 6.28/2.27  Abstraction          : 0.04
% 6.28/2.27  MUC search           : 0.00
% 6.28/2.27  Cooper               : 0.00
% 6.28/2.27  Total                : 1.51
% 6.28/2.27  Index Insertion      : 0.00
% 6.28/2.27  Index Deletion       : 0.00
% 6.28/2.27  Index Matching       : 0.00
% 6.28/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
