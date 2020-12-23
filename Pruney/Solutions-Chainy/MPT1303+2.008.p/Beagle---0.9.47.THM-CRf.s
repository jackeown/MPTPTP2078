%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:47 EST 2020

% Result     : Theorem 26.11s
% Output     : CNFRefutation 26.11s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 104 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_562,plain,(
    ! [A_134,B_135,C_136] :
      ( k9_subset_1(A_134,B_135,C_136) = k3_xboole_0(B_135,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_579,plain,(
    ! [B_135] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_135,'#skF_6') = k3_xboole_0(B_135,'#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_562])).

tff(c_64,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_591,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_64])).

tff(c_66,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_734,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1(k9_subset_1(A_149,B_150,C_151),k1_zfmisc_1(A_149))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_747,plain,(
    ! [B_135] :
      ( m1_subset_1(k3_xboole_0(B_135,'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_734])).

tff(c_757,plain,(
    ! [B_135] : m1_subset_1(k3_xboole_0(B_135,'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_747])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1604,plain,(
    ! [B_224,A_225,C_226] :
      ( v1_tops_2(B_224,A_225)
      | ~ v1_tops_2(C_226,A_225)
      | ~ r1_tarski(B_224,C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225))))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225))))
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6010,plain,(
    ! [A_482,B_483,A_484] :
      ( v1_tops_2(k4_xboole_0(A_482,B_483),A_484)
      | ~ v1_tops_2(A_482,A_484)
      | ~ m1_subset_1(A_482,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484))))
      | ~ m1_subset_1(k4_xboole_0(A_482,B_483),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484))))
      | ~ l1_pre_topc(A_484) ) ),
    inference(resolution,[status(thm)],[c_22,c_1604])).

tff(c_6034,plain,(
    ! [A_20,B_21,A_484] :
      ( v1_tops_2(k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)),A_484)
      | ~ v1_tops_2(A_20,A_484)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484))))
      | ~ m1_subset_1(k3_xboole_0(A_20,B_21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484))))
      | ~ l1_pre_topc(A_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6010])).

tff(c_63081,plain,(
    ! [A_1581,B_1582,A_1583] :
      ( v1_tops_2(k3_xboole_0(A_1581,B_1582),A_1583)
      | ~ v1_tops_2(A_1581,A_1583)
      | ~ m1_subset_1(A_1581,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1583))))
      | ~ m1_subset_1(k3_xboole_0(A_1581,B_1582),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1583))))
      | ~ l1_pre_topc(A_1583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6034])).

tff(c_63228,plain,(
    ! [B_135] :
      ( v1_tops_2(k3_xboole_0(B_135,'#skF_6'),'#skF_4')
      | ~ v1_tops_2(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_757,c_63081])).

tff(c_108139,plain,(
    ! [B_2055] :
      ( v1_tops_2(k3_xboole_0(B_2055,'#skF_6'),'#skF_4')
      | ~ v1_tops_2(B_2055,'#skF_4')
      | ~ m1_subset_1(B_2055,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_63228])).

tff(c_108275,plain,
    ( v1_tops_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4')
    | ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_108139])).

tff(c_108319,plain,(
    v1_tops_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_108275])).

tff(c_108321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_108319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.11/17.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.11/17.39  
% 26.11/17.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.11/17.39  %$ v1_tops_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 26.11/17.39  
% 26.11/17.39  %Foreground sorts:
% 26.11/17.39  
% 26.11/17.39  
% 26.11/17.39  %Background operators:
% 26.11/17.39  
% 26.11/17.39  
% 26.11/17.39  %Foreground operators:
% 26.11/17.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.11/17.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.11/17.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.11/17.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.11/17.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.11/17.39  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 26.11/17.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.11/17.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 26.11/17.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.11/17.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 26.11/17.39  tff('#skF_5', type, '#skF_5': $i).
% 26.11/17.39  tff('#skF_6', type, '#skF_6': $i).
% 26.11/17.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.11/17.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.11/17.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.11/17.39  tff('#skF_4', type, '#skF_4': $i).
% 26.11/17.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.11/17.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 26.11/17.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.11/17.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.11/17.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.11/17.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.11/17.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.11/17.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 26.11/17.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.11/17.39  
% 26.11/17.40  tff(f_162, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 26.11/17.40  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 26.11/17.40  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 26.11/17.40  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 26.11/17.40  tff(f_70, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 26.11/17.40  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 26.11/17.40  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 26.11/17.40  tff(c_562, plain, (![A_134, B_135, C_136]: (k9_subset_1(A_134, B_135, C_136)=k3_xboole_0(B_135, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.11/17.40  tff(c_579, plain, (![B_135]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')), B_135, '#skF_6')=k3_xboole_0(B_135, '#skF_6'))), inference(resolution, [status(thm)], [c_68, c_562])).
% 26.11/17.40  tff(c_64, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')), '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 26.11/17.40  tff(c_591, plain, (~v1_tops_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_64])).
% 26.11/17.40  tff(c_66, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 26.11/17.40  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 26.11/17.40  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 26.11/17.40  tff(c_734, plain, (![A_149, B_150, C_151]: (m1_subset_1(k9_subset_1(A_149, B_150, C_151), k1_zfmisc_1(A_149)) | ~m1_subset_1(C_151, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 26.11/17.40  tff(c_747, plain, (![B_135]: (m1_subset_1(k3_xboole_0(B_135, '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_579, c_734])).
% 26.11/17.40  tff(c_757, plain, (![B_135]: (m1_subset_1(k3_xboole_0(B_135, '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_747])).
% 26.11/17.40  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 26.11/17.40  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.11/17.40  tff(c_1604, plain, (![B_224, A_225, C_226]: (v1_tops_2(B_224, A_225) | ~v1_tops_2(C_226, A_225) | ~r1_tarski(B_224, C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225)))) | ~m1_subset_1(B_224, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225)))) | ~l1_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_149])).
% 26.11/17.40  tff(c_6010, plain, (![A_482, B_483, A_484]: (v1_tops_2(k4_xboole_0(A_482, B_483), A_484) | ~v1_tops_2(A_482, A_484) | ~m1_subset_1(A_482, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484)))) | ~m1_subset_1(k4_xboole_0(A_482, B_483), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484)))) | ~l1_pre_topc(A_484))), inference(resolution, [status(thm)], [c_22, c_1604])).
% 26.11/17.40  tff(c_6034, plain, (![A_20, B_21, A_484]: (v1_tops_2(k4_xboole_0(A_20, k4_xboole_0(A_20, B_21)), A_484) | ~v1_tops_2(A_20, A_484) | ~m1_subset_1(A_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484)))) | ~m1_subset_1(k3_xboole_0(A_20, B_21), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_484)))) | ~l1_pre_topc(A_484))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6010])).
% 26.11/17.40  tff(c_63081, plain, (![A_1581, B_1582, A_1583]: (v1_tops_2(k3_xboole_0(A_1581, B_1582), A_1583) | ~v1_tops_2(A_1581, A_1583) | ~m1_subset_1(A_1581, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1583)))) | ~m1_subset_1(k3_xboole_0(A_1581, B_1582), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1583)))) | ~l1_pre_topc(A_1583))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6034])).
% 26.11/17.40  tff(c_63228, plain, (![B_135]: (v1_tops_2(k3_xboole_0(B_135, '#skF_6'), '#skF_4') | ~v1_tops_2(B_135, '#skF_4') | ~m1_subset_1(B_135, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_757, c_63081])).
% 26.11/17.40  tff(c_108139, plain, (![B_2055]: (v1_tops_2(k3_xboole_0(B_2055, '#skF_6'), '#skF_4') | ~v1_tops_2(B_2055, '#skF_4') | ~m1_subset_1(B_2055, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_63228])).
% 26.11/17.40  tff(c_108275, plain, (v1_tops_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4') | ~v1_tops_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_108139])).
% 26.11/17.40  tff(c_108319, plain, (v1_tops_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_108275])).
% 26.11/17.40  tff(c_108321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_108319])).
% 26.11/17.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.11/17.40  
% 26.11/17.40  Inference rules
% 26.11/17.40  ----------------------
% 26.11/17.40  #Ref     : 23
% 26.11/17.40  #Sup     : 28421
% 26.11/17.40  #Fact    : 0
% 26.11/17.40  #Define  : 0
% 26.11/17.40  #Split   : 11
% 26.11/17.40  #Chain   : 0
% 26.11/17.40  #Close   : 0
% 26.11/17.40  
% 26.11/17.40  Ordering : KBO
% 26.11/17.40  
% 26.11/17.40  Simplification rules
% 26.11/17.40  ----------------------
% 26.11/17.40  #Subsume      : 10693
% 26.11/17.40  #Demod        : 14329
% 26.11/17.40  #Tautology    : 8940
% 26.11/17.40  #SimpNegUnit  : 537
% 26.11/17.40  #BackRed      : 8
% 26.11/17.40  
% 26.11/17.40  #Partial instantiations: 0
% 26.11/17.40  #Strategies tried      : 1
% 26.11/17.40  
% 26.11/17.40  Timing (in seconds)
% 26.11/17.40  ----------------------
% 26.11/17.40  Preprocessing        : 0.36
% 26.11/17.40  Parsing              : 0.19
% 26.11/17.40  CNF conversion       : 0.03
% 26.11/17.40  Main loop            : 16.28
% 26.11/17.40  Inferencing          : 2.34
% 26.11/17.40  Reduction            : 4.58
% 26.11/17.40  Demodulation         : 3.33
% 26.11/17.40  BG Simplification    : 0.22
% 26.11/17.40  Subsumption          : 8.10
% 26.11/17.40  Abstraction          : 0.35
% 26.11/17.40  MUC search           : 0.00
% 26.11/17.40  Cooper               : 0.00
% 26.11/17.40  Total                : 16.67
% 26.11/17.40  Index Insertion      : 0.00
% 26.11/17.40  Index Deletion       : 0.00
% 26.11/17.40  Index Matching       : 0.00
% 26.11/17.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
