%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 173 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [B_172,A_174,E_173,C_170,D_171] : k4_enumset1(A_174,A_174,B_172,C_170,D_171,E_173) = k3_enumset1(A_174,B_172,C_170,D_171,E_173) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [D_36,H_42,E_37,A_33,B_34,C_35] : r2_hidden(H_42,k4_enumset1(A_33,B_34,C_35,D_36,E_37,H_42)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_356,plain,(
    ! [E_206,D_204,A_203,B_205,C_202] : r2_hidden(E_206,k3_enumset1(A_203,B_205,C_202,D_204,E_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_20])).

tff(c_372,plain,(
    ! [D_213,A_214,B_215,C_216] : r2_hidden(D_213,k2_enumset1(A_214,B_215,C_216,D_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_356])).

tff(c_379,plain,(
    ! [C_217,A_218,B_219] : r2_hidden(C_217,k1_enumset1(A_218,B_219,C_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_372])).

tff(c_386,plain,(
    ! [B_220,A_221] : r2_hidden(B_220,k2_tarski(A_221,B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_379])).

tff(c_96,plain,(
    ! [A_66,B_67] : k1_setfam_1(k2_tarski(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k1_setfam_1(B_48),A_47)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,(
    ! [A_66,B_67,A_47] :
      ( r1_tarski(k3_xboole_0(A_66,B_67),A_47)
      | ~ r2_hidden(A_47,k2_tarski(A_66,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_66])).

tff(c_392,plain,(
    ! [A_221,B_220] : r1_tarski(k3_xboole_0(A_221,B_220),B_220) ),
    inference(resolution,[status(thm)],[c_386,c_102])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ! [A_70,B_71] :
      ( v1_relat_1(A_70)
      | ~ v1_relat_1(B_71)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_121,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70,plain,(
    ! [A_52,B_54] :
      ( r1_tarski(k2_relat_1(A_52),k2_relat_1(B_54))
      | ~ r1_tarski(A_52,B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_158,plain,(
    ! [A_118,B_119,C_120] :
      ( r1_tarski(A_118,k3_xboole_0(B_119,C_120))
      | ~ r1_tarski(A_118,C_120)
      | ~ r1_tarski(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_166,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_158,c_74])).

tff(c_186,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_189,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_186])).

tff(c_192,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2,c_189])).

tff(c_195,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_195])).

tff(c_200,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_204,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_200])).

tff(c_207,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_204])).

tff(c_218,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_221,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_221])).

tff(c_226,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.38  
% 2.89/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.89/1.39  
% 2.89/1.40  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.89/1.40  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.89/1.40  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.89/1.40  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.89/1.40  tff(f_69, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.89/1.40  tff(f_71, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.89/1.40  tff(f_79, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.89/1.40  tff(f_105, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.89/1.40  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.89/1.40  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.40  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.89/1.40  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.89/1.40  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.89/1.40  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.40  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.40  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.40  tff(c_248, plain, (![B_172, A_174, E_173, C_170, D_171]: (k4_enumset1(A_174, A_174, B_172, C_170, D_171, E_173)=k3_enumset1(A_174, B_172, C_170, D_171, E_173))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.40  tff(c_20, plain, (![D_36, H_42, E_37, A_33, B_34, C_35]: (r2_hidden(H_42, k4_enumset1(A_33, B_34, C_35, D_36, E_37, H_42)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.40  tff(c_356, plain, (![E_206, D_204, A_203, B_205, C_202]: (r2_hidden(E_206, k3_enumset1(A_203, B_205, C_202, D_204, E_206)))), inference(superposition, [status(thm), theory('equality')], [c_248, c_20])).
% 2.89/1.40  tff(c_372, plain, (![D_213, A_214, B_215, C_216]: (r2_hidden(D_213, k2_enumset1(A_214, B_215, C_216, D_213)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_356])).
% 2.89/1.40  tff(c_379, plain, (![C_217, A_218, B_219]: (r2_hidden(C_217, k1_enumset1(A_218, B_219, C_217)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_372])).
% 2.89/1.40  tff(c_386, plain, (![B_220, A_221]: (r2_hidden(B_220, k2_tarski(A_221, B_220)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_379])).
% 2.89/1.40  tff(c_96, plain, (![A_66, B_67]: (k1_setfam_1(k2_tarski(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.40  tff(c_66, plain, (![B_48, A_47]: (r1_tarski(k1_setfam_1(B_48), A_47) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.89/1.40  tff(c_102, plain, (![A_66, B_67, A_47]: (r1_tarski(k3_xboole_0(A_66, B_67), A_47) | ~r2_hidden(A_47, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_66])).
% 2.89/1.40  tff(c_392, plain, (![A_221, B_220]: (r1_tarski(k3_xboole_0(A_221, B_220), B_220))), inference(resolution, [status(thm)], [c_386, c_102])).
% 2.89/1.40  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.89/1.40  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.40  tff(c_64, plain, (![A_45, B_46]: (m1_subset_1(A_45, k1_zfmisc_1(B_46)) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.40  tff(c_108, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.89/1.40  tff(c_113, plain, (![A_70, B_71]: (v1_relat_1(A_70) | ~v1_relat_1(B_71) | ~r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_64, c_108])).
% 2.89/1.40  tff(c_121, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.89/1.40  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.89/1.40  tff(c_70, plain, (![A_52, B_54]: (r1_tarski(k2_relat_1(A_52), k2_relat_1(B_54)) | ~r1_tarski(A_52, B_54) | ~v1_relat_1(B_54) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.89/1.40  tff(c_158, plain, (![A_118, B_119, C_120]: (r1_tarski(A_118, k3_xboole_0(B_119, C_120)) | ~r1_tarski(A_118, C_120) | ~r1_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.40  tff(c_74, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.89/1.40  tff(c_166, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_158, c_74])).
% 2.89/1.40  tff(c_186, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.89/1.40  tff(c_189, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_186])).
% 2.89/1.40  tff(c_192, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2, c_189])).
% 2.89/1.40  tff(c_195, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_192])).
% 2.89/1.40  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_195])).
% 2.89/1.40  tff(c_200, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_166])).
% 2.89/1.40  tff(c_204, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_200])).
% 2.89/1.40  tff(c_207, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_204])).
% 2.89/1.40  tff(c_218, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_207])).
% 2.89/1.40  tff(c_221, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_218])).
% 2.89/1.40  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_221])).
% 2.89/1.40  tff(c_226, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_207])).
% 2.89/1.40  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_226])).
% 2.89/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.40  
% 2.89/1.40  Inference rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Ref     : 0
% 2.89/1.40  #Sup     : 73
% 2.89/1.40  #Fact    : 0
% 2.89/1.40  #Define  : 0
% 2.89/1.40  #Split   : 3
% 2.89/1.40  #Chain   : 0
% 2.89/1.40  #Close   : 0
% 2.89/1.40  
% 2.89/1.40  Ordering : KBO
% 2.89/1.40  
% 2.89/1.40  Simplification rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Subsume      : 2
% 2.89/1.40  #Demod        : 11
% 2.89/1.40  #Tautology    : 15
% 2.89/1.40  #SimpNegUnit  : 0
% 2.89/1.40  #BackRed      : 1
% 2.89/1.40  
% 2.89/1.40  #Partial instantiations: 0
% 2.89/1.40  #Strategies tried      : 1
% 2.89/1.40  
% 2.89/1.40  Timing (in seconds)
% 2.89/1.40  ----------------------
% 2.89/1.41  Preprocessing        : 0.35
% 2.89/1.41  Parsing              : 0.17
% 2.89/1.41  CNF conversion       : 0.03
% 2.89/1.41  Main loop            : 0.28
% 2.89/1.41  Inferencing          : 0.09
% 2.89/1.41  Reduction            : 0.08
% 2.89/1.41  Demodulation         : 0.06
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.07
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.66
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
