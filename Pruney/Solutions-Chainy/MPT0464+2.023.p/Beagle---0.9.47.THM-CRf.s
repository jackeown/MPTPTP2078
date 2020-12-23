%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   35 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 206 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_68,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_133,B_134,C_135,D_136] : k3_enumset1(A_133,A_133,B_134,C_135,D_136) = k2_enumset1(A_133,B_134,C_135,D_136) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [D_36,A_33,B_34,G_41,C_35] : r2_hidden(G_41,k3_enumset1(A_33,B_34,C_35,D_36,G_41)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_236,plain,(
    ! [D_156,A_157,B_158,C_159] : r2_hidden(D_156,k2_enumset1(A_157,B_158,C_159,D_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_20])).

tff(c_243,plain,(
    ! [C_160,A_161,B_162] : r2_hidden(C_160,k1_enumset1(A_161,B_162,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_236])).

tff(c_250,plain,(
    ! [B_163,A_164] : r2_hidden(B_163,k2_tarski(A_164,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_243])).

tff(c_60,plain,(
    ! [B_47,A_46] :
      ( r1_tarski(k1_setfam_1(B_47),A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_108,plain,(
    ! [A_81,B_82] :
      ( v1_relat_1(A_81)
      | ~ v1_relat_1(B_82)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_58,c_103])).

tff(c_115,plain,(
    ! [B_47,A_46] :
      ( v1_relat_1(k1_setfam_1(B_47))
      | ~ v1_relat_1(A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_60,c_108])).

tff(c_255,plain,(
    ! [A_164,B_163] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_164,B_163)))
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_250,c_115])).

tff(c_258,plain,(
    ! [A_164,B_163] :
      ( v1_relat_1(k3_xboole_0(A_164,B_163))
      | ~ v1_relat_1(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_255])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,(
    ! [A_70,B_71] : k1_setfam_1(k2_tarski(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    ! [A_70,B_71,A_46] :
      ( r1_tarski(k3_xboole_0(A_70,B_71),A_46)
      | ~ r2_hidden(A_46,k2_tarski(A_70,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_60])).

tff(c_256,plain,(
    ! [A_164,B_163] : r1_tarski(k3_xboole_0(A_164,B_163),B_163) ),
    inference(resolution,[status(thm)],[c_250,c_91])).

tff(c_393,plain,(
    ! [C_239,A_240,B_241] :
      ( r1_tarski(k5_relat_1(C_239,A_240),k5_relat_1(C_239,B_241))
      | ~ r1_tarski(A_240,B_241)
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1(B_241)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_316,plain,(
    ! [C_201,A_202,B_203] :
      ( r1_tarski(k5_relat_1(C_201,A_202),k5_relat_1(C_201,B_203))
      | ~ r1_tarski(A_202,B_203)
      | ~ v1_relat_1(C_201)
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_212,plain,(
    ! [A_146,B_147,C_148] :
      ( r1_tarski(A_146,k3_xboole_0(B_147,C_148))
      | ~ r1_tarski(A_146,C_148)
      | ~ r1_tarski(A_146,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_220,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_212,c_66])).

tff(c_274,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_319,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_316,c_274])).

tff(c_325,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_2,c_319])).

tff(c_329,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_258,c_325])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_329])).

tff(c_337,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_396,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_393,c_337])).

tff(c_402,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_256,c_396])).

tff(c_406,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_258,c_402])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.46  
% 2.58/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.58/1.47  
% 2.58/1.47  %Foreground sorts:
% 2.58/1.47  
% 2.58/1.47  
% 2.58/1.47  %Background operators:
% 2.58/1.47  
% 2.58/1.47  
% 2.58/1.47  %Foreground operators:
% 2.58/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.47  
% 2.99/1.48  tff(f_106, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.99/1.48  tff(f_68, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.99/1.48  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.48  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.99/1.48  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.99/1.48  tff(f_66, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.99/1.48  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.99/1.48  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.99/1.48  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.99/1.48  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.99/1.48  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.99/1.48  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.99/1.48  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.48  tff(c_54, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.48  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.48  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.48  tff(c_152, plain, (![A_133, B_134, C_135, D_136]: (k3_enumset1(A_133, A_133, B_134, C_135, D_136)=k2_enumset1(A_133, B_134, C_135, D_136))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.48  tff(c_20, plain, (![D_36, A_33, B_34, G_41, C_35]: (r2_hidden(G_41, k3_enumset1(A_33, B_34, C_35, D_36, G_41)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.48  tff(c_236, plain, (![D_156, A_157, B_158, C_159]: (r2_hidden(D_156, k2_enumset1(A_157, B_158, C_159, D_156)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_20])).
% 2.99/1.48  tff(c_243, plain, (![C_160, A_161, B_162]: (r2_hidden(C_160, k1_enumset1(A_161, B_162, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_236])).
% 2.99/1.48  tff(c_250, plain, (![B_163, A_164]: (r2_hidden(B_163, k2_tarski(A_164, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_243])).
% 2.99/1.48  tff(c_60, plain, (![B_47, A_46]: (r1_tarski(k1_setfam_1(B_47), A_46) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.48  tff(c_58, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.99/1.48  tff(c_103, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.99/1.48  tff(c_108, plain, (![A_81, B_82]: (v1_relat_1(A_81) | ~v1_relat_1(B_82) | ~r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_58, c_103])).
% 2.99/1.48  tff(c_115, plain, (![B_47, A_46]: (v1_relat_1(k1_setfam_1(B_47)) | ~v1_relat_1(A_46) | ~r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_60, c_108])).
% 2.99/1.48  tff(c_255, plain, (![A_164, B_163]: (v1_relat_1(k1_setfam_1(k2_tarski(A_164, B_163))) | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_250, c_115])).
% 2.99/1.48  tff(c_258, plain, (![A_164, B_163]: (v1_relat_1(k3_xboole_0(A_164, B_163)) | ~v1_relat_1(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_255])).
% 2.99/1.48  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.48  tff(c_85, plain, (![A_70, B_71]: (k1_setfam_1(k2_tarski(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.48  tff(c_91, plain, (![A_70, B_71, A_46]: (r1_tarski(k3_xboole_0(A_70, B_71), A_46) | ~r2_hidden(A_46, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_60])).
% 2.99/1.48  tff(c_256, plain, (![A_164, B_163]: (r1_tarski(k3_xboole_0(A_164, B_163), B_163))), inference(resolution, [status(thm)], [c_250, c_91])).
% 2.99/1.48  tff(c_393, plain, (![C_239, A_240, B_241]: (r1_tarski(k5_relat_1(C_239, A_240), k5_relat_1(C_239, B_241)) | ~r1_tarski(A_240, B_241) | ~v1_relat_1(C_239) | ~v1_relat_1(B_241) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.48  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.48  tff(c_316, plain, (![C_201, A_202, B_203]: (r1_tarski(k5_relat_1(C_201, A_202), k5_relat_1(C_201, B_203)) | ~r1_tarski(A_202, B_203) | ~v1_relat_1(C_201) | ~v1_relat_1(B_203) | ~v1_relat_1(A_202))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.48  tff(c_212, plain, (![A_146, B_147, C_148]: (r1_tarski(A_146, k3_xboole_0(B_147, C_148)) | ~r1_tarski(A_146, C_148) | ~r1_tarski(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.48  tff(c_66, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.48  tff(c_220, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_212, c_66])).
% 2.99/1.48  tff(c_274, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.99/1.48  tff(c_319, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_316, c_274])).
% 2.99/1.48  tff(c_325, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_2, c_319])).
% 2.99/1.48  tff(c_329, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_258, c_325])).
% 2.99/1.48  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_329])).
% 2.99/1.48  tff(c_337, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_220])).
% 2.99/1.48  tff(c_396, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_393, c_337])).
% 2.99/1.48  tff(c_402, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_256, c_396])).
% 2.99/1.48  tff(c_406, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_258, c_402])).
% 2.99/1.48  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_406])).
% 2.99/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.48  
% 2.99/1.48  Inference rules
% 2.99/1.48  ----------------------
% 2.99/1.48  #Ref     : 0
% 2.99/1.48  #Sup     : 77
% 2.99/1.48  #Fact    : 0
% 2.99/1.48  #Define  : 0
% 2.99/1.48  #Split   : 2
% 2.99/1.48  #Chain   : 0
% 2.99/1.48  #Close   : 0
% 2.99/1.48  
% 2.99/1.48  Ordering : KBO
% 2.99/1.48  
% 2.99/1.48  Simplification rules
% 2.99/1.48  ----------------------
% 2.99/1.48  #Subsume      : 14
% 2.99/1.48  #Demod        : 22
% 2.99/1.48  #Tautology    : 21
% 2.99/1.48  #SimpNegUnit  : 0
% 2.99/1.48  #BackRed      : 0
% 2.99/1.48  
% 2.99/1.48  #Partial instantiations: 0
% 2.99/1.48  #Strategies tried      : 1
% 2.99/1.48  
% 2.99/1.48  Timing (in seconds)
% 2.99/1.48  ----------------------
% 2.99/1.49  Preprocessing        : 0.38
% 2.99/1.49  Parsing              : 0.19
% 2.99/1.49  CNF conversion       : 0.03
% 2.99/1.49  Main loop            : 0.29
% 2.99/1.49  Inferencing          : 0.10
% 2.99/1.49  Reduction            : 0.08
% 2.99/1.49  Demodulation         : 0.06
% 2.99/1.49  BG Simplification    : 0.02
% 2.99/1.49  Subsumption          : 0.07
% 2.99/1.49  Abstraction          : 0.02
% 2.99/1.49  MUC search           : 0.00
% 2.99/1.49  Cooper               : 0.00
% 2.99/1.49  Total                : 0.70
% 2.99/1.49  Index Insertion      : 0.00
% 2.99/1.49  Index Deletion       : 0.00
% 2.99/1.49  Index Matching       : 0.00
% 2.99/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
