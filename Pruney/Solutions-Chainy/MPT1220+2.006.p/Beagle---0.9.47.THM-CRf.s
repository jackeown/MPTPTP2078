%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 375 expanded)
%              Number of leaves         :   33 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  108 ( 645 expanded)
%              Number of equality atoms :   22 ( 173 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k1_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47,plain,(
    ! [A_29] :
      ( k1_struct_0(A_29) = k1_xboole_0
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [A_32] :
      ( k1_struct_0(A_32) = k1_xboole_0
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_57,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_107,plain,(
    ! [A_48] :
      ( m1_subset_1(k1_struct_0(A_48),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_107])).

tff(c_123,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_126,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_126])).

tff(c_132,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_181,plain,(
    ! [A_61] :
      ( k3_subset_1(u1_struct_0(A_61),k1_struct_0(A_61)) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_190,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_181])).

tff(c_194,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_190])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [B_59,A_60] :
      ( ~ r1_tarski(B_59,'#skF_1'(A_60,B_59))
      | r1_xboole_0(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_97,c_26])).

tff(c_195,plain,(
    ! [A_62] : r1_xboole_0(A_62,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_202,plain,(
    ! [A_62] : k4_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(resolution,[status(thm)],[c_195,c_16])).

tff(c_131,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_250,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_253,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k1_xboole_0) = k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_131,c_250])).

tff(c_261,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_202,c_253])).

tff(c_447,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k2_pre_topc(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_461,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_pre_topc(A_86,B_87),u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_447,c_22])).

tff(c_326,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,k2_pre_topc(A_74,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_328,plain,(
    ! [B_73] :
      ( r1_tarski(B_73,k2_pre_topc('#skF_2',B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_326])).

tff(c_374,plain,(
    ! [B_79] :
      ( r1_tarski(B_79,k2_pre_topc('#skF_2',B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_328])).

tff(c_383,plain,(
    ! [A_80] :
      ( r1_tarski(A_80,k2_pre_topc('#skF_2',A_80))
      | ~ r1_tarski(A_80,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_374])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_578,plain,(
    ! [A_115] :
      ( k2_pre_topc('#skF_2',A_115) = A_115
      | ~ r1_tarski(k2_pre_topc('#skF_2',A_115),A_115)
      | ~ r1_tarski(A_115,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_383,c_8])).

tff(c_582,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_461,c_578])).

tff(c_589,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_261,c_261,c_12,c_261,c_261,c_261,c_582])).

tff(c_590,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_589])).

tff(c_597,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_590])).

tff(c_601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.49/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.49/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.49/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.49/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.35  
% 2.69/1.37  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.37  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.69/1.37  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.69/1.37  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.69/1.37  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.69/1.37  tff(f_76, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k1_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_struct_0)).
% 2.69/1.37  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.69/1.37  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.37  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.69/1.37  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.69/1.37  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.69/1.37  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/1.37  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.69/1.37  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.69/1.37  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.37  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.37  tff(c_40, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.37  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.37  tff(c_34, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.37  tff(c_47, plain, (![A_29]: (k1_struct_0(A_29)=k1_xboole_0 | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.69/1.37  tff(c_53, plain, (![A_32]: (k1_struct_0(A_32)=k1_xboole_0 | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.69/1.37  tff(c_57, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_53])).
% 2.69/1.37  tff(c_107, plain, (![A_48]: (m1_subset_1(k1_struct_0(A_48), k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.37  tff(c_113, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_107])).
% 2.69/1.37  tff(c_123, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_113])).
% 2.69/1.37  tff(c_126, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_123])).
% 2.69/1.37  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_126])).
% 2.69/1.37  tff(c_132, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_113])).
% 2.69/1.37  tff(c_181, plain, (![A_61]: (k3_subset_1(u1_struct_0(A_61), k1_struct_0(A_61))=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.69/1.37  tff(c_190, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_181])).
% 2.69/1.37  tff(c_194, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_190])).
% 2.69/1.37  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.37  tff(c_97, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.37  tff(c_26, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.37  tff(c_175, plain, (![B_59, A_60]: (~r1_tarski(B_59, '#skF_1'(A_60, B_59)) | r1_xboole_0(A_60, B_59))), inference(resolution, [status(thm)], [c_97, c_26])).
% 2.69/1.37  tff(c_195, plain, (![A_62]: (r1_xboole_0(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_175])).
% 2.69/1.37  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.37  tff(c_202, plain, (![A_62]: (k4_xboole_0(A_62, k1_xboole_0)=A_62)), inference(resolution, [status(thm)], [c_195, c_16])).
% 2.69/1.37  tff(c_131, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_113])).
% 2.69/1.37  tff(c_250, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.37  tff(c_253, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k1_xboole_0)=k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)), inference(resolution, [status(thm)], [c_131, c_250])).
% 2.69/1.37  tff(c_261, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_202, c_253])).
% 2.69/1.37  tff(c_447, plain, (![A_86, B_87]: (m1_subset_1(k2_pre_topc(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.37  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.37  tff(c_461, plain, (![A_86, B_87]: (r1_tarski(k2_pre_topc(A_86, B_87), u1_struct_0(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_447, c_22])).
% 2.69/1.37  tff(c_326, plain, (![B_73, A_74]: (r1_tarski(B_73, k2_pre_topc(A_74, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.37  tff(c_328, plain, (![B_73]: (r1_tarski(B_73, k2_pre_topc('#skF_2', B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_326])).
% 2.69/1.37  tff(c_374, plain, (![B_79]: (r1_tarski(B_79, k2_pre_topc('#skF_2', B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_328])).
% 2.69/1.37  tff(c_383, plain, (![A_80]: (r1_tarski(A_80, k2_pre_topc('#skF_2', A_80)) | ~r1_tarski(A_80, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_374])).
% 2.69/1.37  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.37  tff(c_578, plain, (![A_115]: (k2_pre_topc('#skF_2', A_115)=A_115 | ~r1_tarski(k2_pre_topc('#skF_2', A_115), A_115) | ~r1_tarski(A_115, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_383, c_8])).
% 2.69/1.37  tff(c_582, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_461, c_578])).
% 2.69/1.37  tff(c_589, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_261, c_261, c_12, c_261, c_261, c_261, c_582])).
% 2.69/1.37  tff(c_590, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_589])).
% 2.69/1.37  tff(c_597, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_590])).
% 2.69/1.37  tff(c_601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_597])).
% 2.69/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  Inference rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Ref     : 0
% 2.69/1.37  #Sup     : 120
% 2.69/1.37  #Fact    : 0
% 2.69/1.37  #Define  : 0
% 2.69/1.37  #Split   : 1
% 2.69/1.37  #Chain   : 0
% 2.69/1.37  #Close   : 0
% 2.69/1.37  
% 2.69/1.37  Ordering : KBO
% 2.69/1.37  
% 2.69/1.37  Simplification rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Subsume      : 11
% 2.69/1.37  #Demod        : 85
% 2.69/1.37  #Tautology    : 55
% 2.69/1.37  #SimpNegUnit  : 2
% 2.69/1.37  #BackRed      : 2
% 2.69/1.37  
% 2.69/1.37  #Partial instantiations: 0
% 2.69/1.37  #Strategies tried      : 1
% 2.69/1.37  
% 2.69/1.37  Timing (in seconds)
% 2.69/1.37  ----------------------
% 2.69/1.37  Preprocessing        : 0.31
% 2.69/1.37  Parsing              : 0.17
% 2.69/1.37  CNF conversion       : 0.02
% 2.69/1.37  Main loop            : 0.29
% 2.69/1.37  Inferencing          : 0.11
% 2.69/1.37  Reduction            : 0.08
% 2.69/1.37  Demodulation         : 0.06
% 2.69/1.37  BG Simplification    : 0.01
% 2.69/1.37  Subsumption          : 0.05
% 2.69/1.37  Abstraction          : 0.02
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.64
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.37  Index Matching       : 0.00
% 2.69/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
