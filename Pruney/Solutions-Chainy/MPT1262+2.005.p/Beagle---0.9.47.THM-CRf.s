%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 202 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 496 expanded)
%              Number of equality atoms :   23 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & r1_tarski(B,C) )
                 => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_24,plain,(
    ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_14,c_38])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_108,plain,(
    ! [B_33,A_34] :
      ( v1_tops_1(B_33,A_34)
      | k2_pre_topc(A_34,B_33) != k2_struct_0(A_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,(
    ! [B_33] :
      ( v1_tops_1(B_33,'#skF_1')
      | k2_pre_topc('#skF_1',B_33) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_108])).

tff(c_119,plain,(
    ! [B_35] :
      ( v1_tops_1(B_35,'#skF_1')
      | k2_pre_topc('#skF_1',B_35) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_122,plain,
    ( v1_tops_1('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_132,plain,(
    k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_122])).

tff(c_43,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_57,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_51])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_17] :
      ( k2_pre_topc(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_229,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k2_pre_topc(A_41,B_42),k2_pre_topc(A_41,C_43))
      | ~ r1_tarski(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_317,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_pre_topc(A_51,B_52),k2_struct_0(A_51))
      | ~ r1_tarski(B_52,k2_struct_0(A_51))
      | ~ m1_subset_1(k2_struct_0(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_322,plain,(
    ! [B_52] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_52),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_52,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_317])).

tff(c_325,plain,(
    ! [B_52] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_52),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_52,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_56,c_322])).

tff(c_393,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_396,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_396])).

tff(c_426,plain,(
    ! [B_56] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_56),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_56,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_59,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_28,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,(
    ! [A_37,B_38] :
      ( k2_pre_topc(A_37,B_38) = k2_struct_0(A_37)
      | ~ v1_tops_1(B_38,A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,(
    ! [B_38] :
      ( k2_pre_topc('#skF_1',B_38) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_38,'#skF_1')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_178])).

tff(c_189,plain,(
    ! [B_39] :
      ( k2_pre_topc('#skF_1',B_39) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_39,'#skF_1')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_185])).

tff(c_195,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_189])).

tff(c_204,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_195])).

tff(c_234,plain,(
    ! [C_43] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_43))
      | ~ r1_tarski('#skF_2',C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_229])).

tff(c_297,plain,(
    ! [C_50] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_50))
      | ~ r1_tarski('#skF_2',C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59,c_56,c_56,c_234])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_310,plain,(
    ! [C_50] :
      ( k2_pre_topc('#skF_1',C_50) = k2_struct_0('#skF_1')
      | ~ r1_tarski(k2_pre_topc('#skF_1',C_50),k2_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_2',C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_297,c_2])).

tff(c_487,plain,(
    ! [B_58] :
      ( k2_pre_topc('#skF_1',B_58) = k2_struct_0('#skF_1')
      | ~ r1_tarski('#skF_2',B_58)
      | ~ r1_tarski(B_58,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_426,c_310])).

tff(c_493,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_487])).

tff(c_506,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_26,c_493])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  
% 2.48/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.32  %$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.32  
% 2.48/1.32  %Foreground sorts:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Background operators:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Foreground operators:
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.48/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.32  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.48/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.48/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.48/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.32  
% 2.48/1.33  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 2.48/1.33  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.48/1.33  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.48/1.33  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 2.48/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.48/1.33  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.48/1.33  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 2.48/1.33  tff(c_24, plain, (~v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.33  tff(c_38, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.33  tff(c_52, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_14, c_38])).
% 2.48/1.33  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.48/1.33  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 2.48/1.33  tff(c_108, plain, (![B_33, A_34]: (v1_tops_1(B_33, A_34) | k2_pre_topc(A_34, B_33)!=k2_struct_0(A_34) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.33  tff(c_115, plain, (![B_33]: (v1_tops_1(B_33, '#skF_1') | k2_pre_topc('#skF_1', B_33)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_108])).
% 2.48/1.33  tff(c_119, plain, (![B_35]: (v1_tops_1(B_35, '#skF_1') | k2_pre_topc('#skF_1', B_35)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_115])).
% 2.48/1.33  tff(c_122, plain, (v1_tops_1('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_119])).
% 2.48/1.33  tff(c_132, plain, (k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_122])).
% 2.48/1.33  tff(c_43, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.33  tff(c_51, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_43])).
% 2.48/1.33  tff(c_57, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_51])).
% 2.48/1.33  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.33  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.33  tff(c_22, plain, (![A_17]: (k2_pre_topc(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.48/1.33  tff(c_229, plain, (![A_41, B_42, C_43]: (r1_tarski(k2_pre_topc(A_41, B_42), k2_pre_topc(A_41, C_43)) | ~r1_tarski(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.33  tff(c_317, plain, (![A_51, B_52]: (r1_tarski(k2_pre_topc(A_51, B_52), k2_struct_0(A_51)) | ~r1_tarski(B_52, k2_struct_0(A_51)) | ~m1_subset_1(k2_struct_0(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~l1_pre_topc(A_51))), inference(superposition, [status(thm), theory('equality')], [c_22, c_229])).
% 2.48/1.33  tff(c_322, plain, (![B_52]: (r1_tarski(k2_pre_topc('#skF_1', B_52), k2_struct_0('#skF_1')) | ~r1_tarski(B_52, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_317])).
% 2.48/1.33  tff(c_325, plain, (![B_52]: (r1_tarski(k2_pre_topc('#skF_1', B_52), k2_struct_0('#skF_1')) | ~r1_tarski(B_52, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_56, c_322])).
% 2.48/1.33  tff(c_393, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_325])).
% 2.48/1.33  tff(c_396, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_393])).
% 2.48/1.33  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_396])).
% 2.48/1.33  tff(c_426, plain, (![B_56]: (r1_tarski(k2_pre_topc('#skF_1', B_56), k2_struct_0('#skF_1')) | ~r1_tarski(B_56, k2_struct_0('#skF_1')) | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_325])).
% 2.48/1.33  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_59, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 2.48/1.33  tff(c_28, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.33  tff(c_178, plain, (![A_37, B_38]: (k2_pre_topc(A_37, B_38)=k2_struct_0(A_37) | ~v1_tops_1(B_38, A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.33  tff(c_185, plain, (![B_38]: (k2_pre_topc('#skF_1', B_38)=k2_struct_0('#skF_1') | ~v1_tops_1(B_38, '#skF_1') | ~m1_subset_1(B_38, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_178])).
% 2.48/1.33  tff(c_189, plain, (![B_39]: (k2_pre_topc('#skF_1', B_39)=k2_struct_0('#skF_1') | ~v1_tops_1(B_39, '#skF_1') | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_185])).
% 2.48/1.33  tff(c_195, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_59, c_189])).
% 2.48/1.33  tff(c_204, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_195])).
% 2.48/1.33  tff(c_234, plain, (![C_43]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_43)) | ~r1_tarski('#skF_2', C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_229])).
% 2.48/1.33  tff(c_297, plain, (![C_50]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_50)) | ~r1_tarski('#skF_2', C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59, c_56, c_56, c_234])).
% 2.48/1.33  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.33  tff(c_310, plain, (![C_50]: (k2_pre_topc('#skF_1', C_50)=k2_struct_0('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', C_50), k2_struct_0('#skF_1')) | ~r1_tarski('#skF_2', C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_297, c_2])).
% 2.48/1.33  tff(c_487, plain, (![B_58]: (k2_pre_topc('#skF_1', B_58)=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', B_58) | ~r1_tarski(B_58, k2_struct_0('#skF_1')) | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_426, c_310])).
% 2.48/1.33  tff(c_493, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_487])).
% 2.48/1.33  tff(c_506, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_26, c_493])).
% 2.48/1.33  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_506])).
% 2.48/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  Inference rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Ref     : 0
% 2.48/1.33  #Sup     : 92
% 2.48/1.33  #Fact    : 0
% 2.48/1.33  #Define  : 0
% 2.48/1.33  #Split   : 5
% 2.48/1.33  #Chain   : 0
% 2.48/1.33  #Close   : 0
% 2.48/1.33  
% 2.48/1.33  Ordering : KBO
% 2.48/1.33  
% 2.48/1.33  Simplification rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Subsume      : 11
% 2.48/1.33  #Demod        : 103
% 2.48/1.33  #Tautology    : 38
% 2.48/1.33  #SimpNegUnit  : 7
% 2.48/1.33  #BackRed      : 4
% 2.48/1.33  
% 2.48/1.33  #Partial instantiations: 0
% 2.48/1.33  #Strategies tried      : 1
% 2.48/1.33  
% 2.48/1.33  Timing (in seconds)
% 2.48/1.33  ----------------------
% 2.48/1.34  Preprocessing        : 0.30
% 2.48/1.34  Parsing              : 0.16
% 2.48/1.34  CNF conversion       : 0.02
% 2.48/1.34  Main loop            : 0.28
% 2.48/1.34  Inferencing          : 0.10
% 2.48/1.34  Reduction            : 0.09
% 2.48/1.34  Demodulation         : 0.06
% 2.48/1.34  BG Simplification    : 0.01
% 2.48/1.34  Subsumption          : 0.06
% 2.48/1.34  Abstraction          : 0.02
% 2.48/1.34  MUC search           : 0.00
% 2.48/1.34  Cooper               : 0.00
% 2.48/1.34  Total                : 0.61
% 2.48/1.34  Index Insertion      : 0.00
% 2.48/1.34  Index Deletion       : 0.00
% 2.48/1.34  Index Matching       : 0.00
% 2.48/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
