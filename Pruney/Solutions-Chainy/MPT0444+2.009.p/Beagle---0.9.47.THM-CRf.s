%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 123 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 209 expanded)
%              Number of equality atoms :   11 (  33 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_68,B_69,C_70] : k2_enumset1(A_68,A_68,B_69,C_70) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [F_22,A_15,B_16,C_17] : r2_hidden(F_22,k2_enumset1(A_15,B_16,C_17,F_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [C_82,A_83,B_84] : r2_hidden(C_82,k1_enumset1(A_83,B_84,C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_14])).

tff(c_152,plain,(
    ! [B_7,A_6] : r2_hidden(B_7,k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_149])).

tff(c_42,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k1_setfam_1(B_46),A_47)
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_349,plain,(
    ! [A_159,B_160,A_161] :
      ( r1_tarski(k3_xboole_0(A_159,B_160),A_161)
      | ~ r2_hidden(A_161,k2_tarski(A_159,B_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_356,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),B_7) ),
    inference(resolution,[status(thm)],[c_152,c_349])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_setfam_1(B_28),A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_99,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(A_66)
      | ~ v1_relat_1(B_67)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_155,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(k1_setfam_1(B_89))
      | ~ v1_relat_1(A_90)
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_157,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,B_7)))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_152,c_155])).

tff(c_175,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_157])).

tff(c_293,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k2_relat_1(A_144),k2_relat_1(B_145))
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k2_relat_1(A_129),k2_relat_1(B_130))
      | ~ r1_tarski(A_129,B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_135,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(A_76,k3_xboole_0(B_77,C_78))
      | ~ r1_tarski(A_76,C_78)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_143,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_135,c_56])).

tff(c_205,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_250,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_247,c_205])).

tff(c_256,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2,c_250])).

tff(c_260,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_256])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_260])).

tff(c_268,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_296,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_293,c_268])).

tff(c_302,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_296])).

tff(c_304,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_307,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_304])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_307])).

tff(c_315,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.30  
% 2.49/1.30  %Foreground sorts:
% 2.49/1.30  
% 2.49/1.30  
% 2.49/1.30  %Background operators:
% 2.49/1.30  
% 2.49/1.30  
% 2.49/1.30  %Foreground operators:
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.49/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.30  
% 2.49/1.32  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.49/1.32  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.49/1.32  tff(f_57, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.49/1.32  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.49/1.32  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.49/1.32  tff(f_93, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.49/1.32  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.49/1.32  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.49/1.32  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.49/1.32  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.49/1.32  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.49/1.32  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.32  tff(c_108, plain, (![A_68, B_69, C_70]: (k2_enumset1(A_68, A_68, B_69, C_70)=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.32  tff(c_14, plain, (![F_22, A_15, B_16, C_17]: (r2_hidden(F_22, k2_enumset1(A_15, B_16, C_17, F_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.32  tff(c_149, plain, (![C_82, A_83, B_84]: (r2_hidden(C_82, k1_enumset1(A_83, B_84, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_14])).
% 2.49/1.32  tff(c_152, plain, (![B_7, A_6]: (r2_hidden(B_7, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_149])).
% 2.49/1.32  tff(c_42, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.32  tff(c_86, plain, (![B_46, A_47]: (r1_tarski(k1_setfam_1(B_46), A_47) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.32  tff(c_349, plain, (![A_159, B_160, A_161]: (r1_tarski(k3_xboole_0(A_159, B_160), A_161) | ~r2_hidden(A_161, k2_tarski(A_159, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_86])).
% 2.49/1.32  tff(c_356, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), B_7))), inference(resolution, [status(thm)], [c_152, c_349])).
% 2.49/1.32  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.49/1.32  tff(c_48, plain, (![B_28, A_27]: (r1_tarski(k1_setfam_1(B_28), A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.32  tff(c_46, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.49/1.32  tff(c_94, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.32  tff(c_99, plain, (![A_66, B_67]: (v1_relat_1(A_66) | ~v1_relat_1(B_67) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_46, c_94])).
% 2.49/1.32  tff(c_155, plain, (![B_89, A_90]: (v1_relat_1(k1_setfam_1(B_89)) | ~v1_relat_1(A_90) | ~r2_hidden(A_90, B_89))), inference(resolution, [status(thm)], [c_48, c_99])).
% 2.49/1.32  tff(c_157, plain, (![A_6, B_7]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, B_7))) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_152, c_155])).
% 2.49/1.32  tff(c_175, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_157])).
% 2.49/1.32  tff(c_293, plain, (![A_144, B_145]: (r1_tarski(k2_relat_1(A_144), k2_relat_1(B_145)) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.49/1.32  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.49/1.32  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.32  tff(c_247, plain, (![A_129, B_130]: (r1_tarski(k2_relat_1(A_129), k2_relat_1(B_130)) | ~r1_tarski(A_129, B_130) | ~v1_relat_1(B_130) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.49/1.32  tff(c_135, plain, (![A_76, B_77, C_78]: (r1_tarski(A_76, k3_xboole_0(B_77, C_78)) | ~r1_tarski(A_76, C_78) | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.32  tff(c_56, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.49/1.32  tff(c_143, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_135, c_56])).
% 2.49/1.32  tff(c_205, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_143])).
% 2.49/1.32  tff(c_250, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_247, c_205])).
% 2.49/1.32  tff(c_256, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2, c_250])).
% 2.49/1.32  tff(c_260, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_175, c_256])).
% 2.49/1.32  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_260])).
% 2.49/1.32  tff(c_268, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_143])).
% 2.49/1.32  tff(c_296, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_293, c_268])).
% 2.49/1.32  tff(c_302, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_296])).
% 2.49/1.32  tff(c_304, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.49/1.32  tff(c_307, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_175, c_304])).
% 2.49/1.32  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_307])).
% 2.49/1.32  tff(c_315, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_302])).
% 2.49/1.32  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_315])).
% 2.49/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  Inference rules
% 2.49/1.32  ----------------------
% 2.49/1.32  #Ref     : 0
% 2.49/1.32  #Sup     : 64
% 2.49/1.32  #Fact    : 0
% 2.49/1.32  #Define  : 0
% 2.49/1.32  #Split   : 3
% 2.49/1.32  #Chain   : 0
% 2.49/1.32  #Close   : 0
% 2.49/1.32  
% 2.49/1.32  Ordering : KBO
% 2.49/1.32  
% 2.49/1.32  Simplification rules
% 2.49/1.32  ----------------------
% 2.49/1.32  #Subsume      : 14
% 2.49/1.32  #Demod        : 16
% 2.49/1.32  #Tautology    : 17
% 2.49/1.32  #SimpNegUnit  : 0
% 2.49/1.32  #BackRed      : 1
% 2.49/1.32  
% 2.49/1.32  #Partial instantiations: 0
% 2.49/1.32  #Strategies tried      : 1
% 2.49/1.32  
% 2.49/1.32  Timing (in seconds)
% 2.49/1.32  ----------------------
% 2.49/1.32  Preprocessing        : 0.31
% 2.49/1.32  Parsing              : 0.16
% 2.49/1.32  CNF conversion       : 0.02
% 2.49/1.32  Main loop            : 0.24
% 2.49/1.32  Inferencing          : 0.09
% 2.49/1.32  Reduction            : 0.07
% 2.49/1.32  Demodulation         : 0.05
% 2.49/1.32  BG Simplification    : 0.01
% 2.49/1.32  Subsumption          : 0.05
% 2.49/1.32  Abstraction          : 0.02
% 2.49/1.32  MUC search           : 0.00
% 2.49/1.32  Cooper               : 0.00
% 2.49/1.32  Total                : 0.59
% 2.49/1.32  Index Insertion      : 0.00
% 2.49/1.32  Index Deletion       : 0.00
% 2.49/1.32  Index Matching       : 0.00
% 2.49/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
