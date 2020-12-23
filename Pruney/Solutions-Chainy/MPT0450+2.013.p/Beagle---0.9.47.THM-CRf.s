%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 122 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 206 expanded)
%              Number of equality atoms :   11 (  33 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_68,B_69,C_70] : k2_enumset1(A_68,A_68,B_69,C_70) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [F_22,A_15,B_16,C_17] : r2_hidden(F_22,k2_enumset1(A_15,B_16,C_17,F_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_127,plain,(
    ! [C_71,A_72,B_73] : r2_hidden(C_71,k1_enumset1(A_72,B_73,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14])).

tff(c_130,plain,(
    ! [B_7,A_6] : r2_hidden(B_7,k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_127])).

tff(c_42,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k1_setfam_1(B_52),A_53)
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_294,plain,(
    ! [A_141,B_142,A_143] :
      ( r1_tarski(k3_xboole_0(A_141,B_142),A_143)
      | ~ r2_hidden(A_143,k2_tarski(A_141,B_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_77])).

tff(c_303,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),B_7) ),
    inference(resolution,[status(thm)],[c_130,c_294])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

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

tff(c_92,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_97,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(A_66)
      | ~ v1_relat_1(B_67)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_153,plain,(
    ! [B_90,A_91] :
      ( v1_relat_1(k1_setfam_1(B_90))
      | ~ v1_relat_1(A_91)
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_161,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,B_7)))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_130,c_153])).

tff(c_177,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_161])).

tff(c_266,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k3_relat_1(A_135),k3_relat_1(B_136))
      | ~ r1_tarski(A_135,B_136)
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_221,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k3_relat_1(A_118),k3_relat_1(B_119))
      | ~ r1_tarski(A_118,B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_183,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(A_92,k3_xboole_0(B_93,C_94))
      | ~ r1_tarski(A_92,C_94)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_191,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_183,c_54])).

tff(c_203,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_224,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_221,c_203])).

tff(c_230,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2,c_224])).

tff(c_234,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_230])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_234])).

tff(c_242,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_269,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_266,c_242])).

tff(c_275,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_269])).

tff(c_277,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_280,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_277])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_280])).

tff(c_288,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.53  
% 2.79/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.53  
% 2.79/1.53  %Foreground sorts:
% 2.79/1.53  
% 2.79/1.53  
% 2.79/1.53  %Background operators:
% 2.79/1.53  
% 2.79/1.53  
% 2.79/1.53  %Foreground operators:
% 2.79/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.79/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.53  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.79/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.79/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.53  
% 2.83/1.55  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.83/1.55  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.83/1.55  tff(f_57, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.83/1.55  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.83/1.55  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.83/1.55  tff(f_91, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.83/1.55  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.55  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.55  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.83/1.55  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.83/1.55  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.83/1.55  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.55  tff(c_106, plain, (![A_68, B_69, C_70]: (k2_enumset1(A_68, A_68, B_69, C_70)=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.55  tff(c_14, plain, (![F_22, A_15, B_16, C_17]: (r2_hidden(F_22, k2_enumset1(A_15, B_16, C_17, F_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.83/1.55  tff(c_127, plain, (![C_71, A_72, B_73]: (r2_hidden(C_71, k1_enumset1(A_72, B_73, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_14])).
% 2.83/1.55  tff(c_130, plain, (![B_7, A_6]: (r2_hidden(B_7, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_127])).
% 2.83/1.55  tff(c_42, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.55  tff(c_77, plain, (![B_52, A_53]: (r1_tarski(k1_setfam_1(B_52), A_53) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.55  tff(c_294, plain, (![A_141, B_142, A_143]: (r1_tarski(k3_xboole_0(A_141, B_142), A_143) | ~r2_hidden(A_143, k2_tarski(A_141, B_142)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_77])).
% 2.83/1.55  tff(c_303, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), B_7))), inference(resolution, [status(thm)], [c_130, c_294])).
% 2.83/1.55  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.83/1.55  tff(c_48, plain, (![B_28, A_27]: (r1_tarski(k1_setfam_1(B_28), A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.55  tff(c_46, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.55  tff(c_92, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.83/1.55  tff(c_97, plain, (![A_66, B_67]: (v1_relat_1(A_66) | ~v1_relat_1(B_67) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_46, c_92])).
% 2.83/1.55  tff(c_153, plain, (![B_90, A_91]: (v1_relat_1(k1_setfam_1(B_90)) | ~v1_relat_1(A_91) | ~r2_hidden(A_91, B_90))), inference(resolution, [status(thm)], [c_48, c_97])).
% 2.83/1.55  tff(c_161, plain, (![A_6, B_7]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, B_7))) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_130, c_153])).
% 2.83/1.55  tff(c_177, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_161])).
% 2.83/1.55  tff(c_266, plain, (![A_135, B_136]: (r1_tarski(k3_relat_1(A_135), k3_relat_1(B_136)) | ~r1_tarski(A_135, B_136) | ~v1_relat_1(B_136) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.55  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.83/1.55  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.55  tff(c_221, plain, (![A_118, B_119]: (r1_tarski(k3_relat_1(A_118), k3_relat_1(B_119)) | ~r1_tarski(A_118, B_119) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.55  tff(c_183, plain, (![A_92, B_93, C_94]: (r1_tarski(A_92, k3_xboole_0(B_93, C_94)) | ~r1_tarski(A_92, C_94) | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.55  tff(c_54, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.83/1.55  tff(c_191, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_183, c_54])).
% 2.83/1.55  tff(c_203, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_191])).
% 2.83/1.55  tff(c_224, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_221, c_203])).
% 2.83/1.55  tff(c_230, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2, c_224])).
% 2.83/1.55  tff(c_234, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_230])).
% 2.83/1.55  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_234])).
% 2.83/1.55  tff(c_242, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_191])).
% 2.83/1.55  tff(c_269, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_266, c_242])).
% 2.83/1.55  tff(c_275, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_269])).
% 2.83/1.55  tff(c_277, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_275])).
% 2.83/1.55  tff(c_280, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_277])).
% 2.83/1.55  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_280])).
% 2.83/1.55  tff(c_288, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_275])).
% 2.83/1.55  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_303, c_288])).
% 2.83/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.55  
% 2.83/1.55  Inference rules
% 2.83/1.55  ----------------------
% 2.83/1.55  #Ref     : 0
% 2.83/1.55  #Sup     : 53
% 2.83/1.55  #Fact    : 0
% 2.83/1.55  #Define  : 0
% 2.83/1.55  #Split   : 3
% 2.83/1.55  #Chain   : 0
% 2.83/1.55  #Close   : 0
% 2.83/1.55  
% 2.83/1.55  Ordering : KBO
% 2.83/1.55  
% 2.83/1.55  Simplification rules
% 2.83/1.55  ----------------------
% 2.83/1.55  #Subsume      : 12
% 2.83/1.55  #Demod        : 15
% 2.83/1.55  #Tautology    : 12
% 2.83/1.55  #SimpNegUnit  : 0
% 2.83/1.55  #BackRed      : 1
% 2.83/1.55  
% 2.83/1.55  #Partial instantiations: 0
% 2.83/1.55  #Strategies tried      : 1
% 2.83/1.55  
% 2.83/1.55  Timing (in seconds)
% 2.83/1.55  ----------------------
% 2.83/1.56  Preprocessing        : 0.46
% 2.83/1.56  Parsing              : 0.26
% 2.83/1.56  CNF conversion       : 0.03
% 2.83/1.56  Main loop            : 0.31
% 2.83/1.56  Inferencing          : 0.12
% 2.83/1.56  Reduction            : 0.08
% 2.83/1.56  Demodulation         : 0.06
% 2.83/1.56  BG Simplification    : 0.02
% 2.83/1.56  Subsumption          : 0.07
% 2.83/1.56  Abstraction          : 0.02
% 2.83/1.56  MUC search           : 0.00
% 2.83/1.56  Cooper               : 0.00
% 2.83/1.56  Total                : 0.82
% 2.83/1.56  Index Insertion      : 0.00
% 2.83/1.56  Index Deletion       : 0.00
% 2.83/1.56  Index Matching       : 0.00
% 2.83/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
