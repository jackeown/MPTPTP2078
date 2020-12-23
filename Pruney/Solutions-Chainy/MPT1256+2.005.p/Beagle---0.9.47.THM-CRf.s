%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:57 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 131 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 247 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k1_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

tff(c_18,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_34,B_35] :
      ( k2_tops_1(A_34,k3_subset_1(u1_struct_0(A_34),B_35)) = k2_tops_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_101,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_109,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_105])).

tff(c_111,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_114,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_111])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_120,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_23,plain,(
    ! [A_23,B_24] :
      ( k3_subset_1(A_23,k3_subset_1(A_23,B_24)) = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_258,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(u1_struct_0(A_40),k2_pre_topc(A_40,k3_subset_1(u1_struct_0(A_40),B_41))) = k1_tops_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_289,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_258])).

tff(c_297,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120,c_289])).

tff(c_119,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_221,plain,(
    ! [A_38,B_39] :
      ( k4_subset_1(u1_struct_0(A_38),B_39,k2_tops_1(A_38,B_39)) = k2_pre_topc(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_239,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_221])).

tff(c_257,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_239])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k4_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_301,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_4])).

tff(c_305,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_119,c_301])).

tff(c_12,plain,(
    ! [A_13,B_15] :
      ( k2_tops_1(A_13,k3_subset_1(u1_struct_0(A_13),B_15)) = k2_tops_1(A_13,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_310,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_305,c_12])).

tff(c_318,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_310])).

tff(c_372,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_318])).

tff(c_138,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k2_tops_1(A_36,k1_tops_1(A_36,B_37)),k2_tops_1(A_36,B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_138])).

tff(c_143,plain,(
    r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120,c_141])).

tff(c_373,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_143])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:15:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.20/1.31  
% 2.20/1.31  %Foreground sorts:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Background operators:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Foreground operators:
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.31  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.20/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.20/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.20/1.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.20/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.20/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.31  
% 2.56/1.33  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 2.56/1.33  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.56/1.33  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 2.56/1.33  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.56/1.33  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.56/1.33  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.56/1.33  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.56/1.33  tff(f_35, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.56/1.33  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k1_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_tops_1)).
% 2.56/1.33  tff(c_18, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.33  tff(c_85, plain, (![A_34, B_35]: (k2_tops_1(A_34, k3_subset_1(u1_struct_0(A_34), B_35))=k2_tops_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.33  tff(c_95, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_85])).
% 2.56/1.33  tff(c_101, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_95])).
% 2.56/1.33  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(k2_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_105, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 2.56/1.33  tff(c_109, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_105])).
% 2.56/1.33  tff(c_111, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_109])).
% 2.56/1.33  tff(c_114, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_111])).
% 2.56/1.33  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_114])).
% 2.56/1.33  tff(c_120, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_109])).
% 2.56/1.33  tff(c_23, plain, (![A_23, B_24]: (k3_subset_1(A_23, k3_subset_1(A_23, B_24))=B_24 | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.33  tff(c_26, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_23])).
% 2.56/1.33  tff(c_258, plain, (![A_40, B_41]: (k3_subset_1(u1_struct_0(A_40), k2_pre_topc(A_40, k3_subset_1(u1_struct_0(A_40), B_41)))=k1_tops_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.33  tff(c_289, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_258])).
% 2.56/1.33  tff(c_297, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120, c_289])).
% 2.56/1.33  tff(c_119, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_109])).
% 2.56/1.33  tff(c_221, plain, (![A_38, B_39]: (k4_subset_1(u1_struct_0(A_38), B_39, k2_tops_1(A_38, B_39))=k2_pre_topc(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.33  tff(c_239, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_221])).
% 2.56/1.33  tff(c_257, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_239])).
% 2.56/1.33  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k4_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.33  tff(c_301, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_257, c_4])).
% 2.56/1.33  tff(c_305, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_119, c_301])).
% 2.56/1.33  tff(c_12, plain, (![A_13, B_15]: (k2_tops_1(A_13, k3_subset_1(u1_struct_0(A_13), B_15))=k2_tops_1(A_13, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.33  tff(c_310, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_305, c_12])).
% 2.56/1.33  tff(c_318, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_310])).
% 2.56/1.33  tff(c_372, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_318])).
% 2.56/1.33  tff(c_138, plain, (![A_36, B_37]: (r1_tarski(k2_tops_1(A_36, k1_tops_1(A_36, B_37)), k2_tops_1(A_36, B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.56/1.33  tff(c_141, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_138])).
% 2.56/1.33  tff(c_143, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120, c_141])).
% 2.56/1.33  tff(c_373, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_143])).
% 2.56/1.33  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_373])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 85
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 2
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 1
% 2.56/1.33  #Demod        : 62
% 2.56/1.33  #Tautology    : 39
% 2.56/1.33  #SimpNegUnit  : 1
% 2.56/1.33  #BackRed      : 1
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.29
% 2.56/1.33  Parsing              : 0.16
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.28
% 2.56/1.33  Inferencing          : 0.10
% 2.56/1.33  Reduction            : 0.09
% 2.56/1.33  Demodulation         : 0.07
% 2.56/1.33  BG Simplification    : 0.02
% 2.56/1.33  Subsumption          : 0.05
% 2.56/1.33  Abstraction          : 0.02
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.61
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
