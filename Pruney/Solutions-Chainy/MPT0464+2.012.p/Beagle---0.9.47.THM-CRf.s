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
% DateTime   : Thu Dec  3 09:58:44 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 176 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_71,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(A_77)
      | ~ v1_relat_1(B_78)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_141,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_526,plain,(
    ! [C_215,E_219,A_216,B_217,D_218] : k4_enumset1(A_216,A_216,B_217,C_215,D_218,E_219) = k3_enumset1(A_216,B_217,C_215,D_218,E_219) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [E_26,H_31,A_22,B_23,D_25,C_24] : r2_hidden(H_31,k4_enumset1(A_22,B_23,C_24,D_25,E_26,H_31)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_683,plain,(
    ! [D_268,B_267,C_271,E_269,A_270] : r2_hidden(E_269,k3_enumset1(A_270,B_267,C_271,D_268,E_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_22])).

tff(c_690,plain,(
    ! [D_272,A_273,B_274,C_275] : r2_hidden(D_272,k2_enumset1(A_273,B_274,C_275,D_272)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_683])).

tff(c_697,plain,(
    ! [C_276,A_277,B_278] : r2_hidden(C_276,k1_enumset1(A_277,B_278,C_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_690])).

tff(c_704,plain,(
    ! [B_279,A_280] : r2_hidden(B_279,k2_tarski(A_280,B_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_697])).

tff(c_100,plain,(
    ! [A_71,B_72] : k1_setfam_1(k2_tarski(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k1_setfam_1(B_37),A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_106,plain,(
    ! [A_71,B_72,A_36] :
      ( r1_tarski(k3_xboole_0(A_71,B_72),A_36)
      | ~ r2_hidden(A_36,k2_tarski(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_68])).

tff(c_710,plain,(
    ! [A_280,B_279] : r1_tarski(k3_xboole_0(A_280,B_279),B_279) ),
    inference(resolution,[status(thm)],[c_704,c_106])).

tff(c_745,plain,(
    ! [A_283,C_284,B_285,D_286] :
      ( r1_tarski(k5_relat_1(A_283,C_284),k5_relat_1(B_285,D_286))
      | ~ r1_tarski(C_284,D_286)
      | ~ r1_tarski(A_283,B_285)
      | ~ v1_relat_1(D_286)
      | ~ v1_relat_1(C_284)
      | ~ v1_relat_1(B_285)
      | ~ v1_relat_1(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_406,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r1_tarski(k5_relat_1(A_166,C_167),k5_relat_1(B_168,D_169))
      | ~ r1_tarski(C_167,D_169)
      | ~ r1_tarski(A_166,B_168)
      | ~ v1_relat_1(D_169)
      | ~ v1_relat_1(C_167)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_205,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(A_126,k3_xboole_0(B_127,C_128))
      | ~ r1_tarski(A_126,C_128)
      | ~ r1_tarski(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_223,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_205,c_74])).

tff(c_301,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_409,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_406,c_301])).

tff(c_420,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_6,c_8,c_409])).

tff(c_426,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_420])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_426])).

tff(c_431,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_751,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_745,c_431])).

tff(c_765,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_6,c_710,c_751])).

tff(c_771,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_765])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.44  
% 2.89/1.44  %Foreground sorts:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Background operators:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Foreground operators:
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.89/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.89/1.44  
% 2.89/1.45  tff(f_116, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.89/1.45  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.89/1.45  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.45  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.89/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.89/1.45  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.89/1.45  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.89/1.45  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.89/1.45  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.89/1.45  tff(f_71, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.89/1.45  tff(f_73, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.89/1.45  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.89/1.45  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 2.89/1.45  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.89/1.45  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.89/1.45  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.45  tff(c_66, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.89/1.45  tff(c_125, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.89/1.45  tff(c_130, plain, (![A_77, B_78]: (v1_relat_1(A_77) | ~v1_relat_1(B_78) | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_66, c_125])).
% 2.89/1.45  tff(c_141, plain, (![A_3, B_4]: (v1_relat_1(k3_xboole_0(A_3, B_4)) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_8, c_130])).
% 2.89/1.45  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.89/1.45  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.89/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.45  tff(c_12, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.45  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.45  tff(c_16, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.45  tff(c_526, plain, (![C_215, E_219, A_216, B_217, D_218]: (k4_enumset1(A_216, A_216, B_217, C_215, D_218, E_219)=k3_enumset1(A_216, B_217, C_215, D_218, E_219))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.45  tff(c_22, plain, (![E_26, H_31, A_22, B_23, D_25, C_24]: (r2_hidden(H_31, k4_enumset1(A_22, B_23, C_24, D_25, E_26, H_31)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.45  tff(c_683, plain, (![D_268, B_267, C_271, E_269, A_270]: (r2_hidden(E_269, k3_enumset1(A_270, B_267, C_271, D_268, E_269)))), inference(superposition, [status(thm), theory('equality')], [c_526, c_22])).
% 2.89/1.45  tff(c_690, plain, (![D_272, A_273, B_274, C_275]: (r2_hidden(D_272, k2_enumset1(A_273, B_274, C_275, D_272)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_683])).
% 2.89/1.45  tff(c_697, plain, (![C_276, A_277, B_278]: (r2_hidden(C_276, k1_enumset1(A_277, B_278, C_276)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_690])).
% 2.89/1.45  tff(c_704, plain, (![B_279, A_280]: (r2_hidden(B_279, k2_tarski(A_280, B_279)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_697])).
% 2.89/1.45  tff(c_100, plain, (![A_71, B_72]: (k1_setfam_1(k2_tarski(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.89/1.45  tff(c_68, plain, (![B_37, A_36]: (r1_tarski(k1_setfam_1(B_37), A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.45  tff(c_106, plain, (![A_71, B_72, A_36]: (r1_tarski(k3_xboole_0(A_71, B_72), A_36) | ~r2_hidden(A_36, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_68])).
% 2.89/1.45  tff(c_710, plain, (![A_280, B_279]: (r1_tarski(k3_xboole_0(A_280, B_279), B_279))), inference(resolution, [status(thm)], [c_704, c_106])).
% 2.89/1.45  tff(c_745, plain, (![A_283, C_284, B_285, D_286]: (r1_tarski(k5_relat_1(A_283, C_284), k5_relat_1(B_285, D_286)) | ~r1_tarski(C_284, D_286) | ~r1_tarski(A_283, B_285) | ~v1_relat_1(D_286) | ~v1_relat_1(C_284) | ~v1_relat_1(B_285) | ~v1_relat_1(A_283))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.89/1.45  tff(c_406, plain, (![A_166, C_167, B_168, D_169]: (r1_tarski(k5_relat_1(A_166, C_167), k5_relat_1(B_168, D_169)) | ~r1_tarski(C_167, D_169) | ~r1_tarski(A_166, B_168) | ~v1_relat_1(D_169) | ~v1_relat_1(C_167) | ~v1_relat_1(B_168) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.89/1.45  tff(c_205, plain, (![A_126, B_127, C_128]: (r1_tarski(A_126, k3_xboole_0(B_127, C_128)) | ~r1_tarski(A_126, C_128) | ~r1_tarski(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.45  tff(c_74, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.89/1.45  tff(c_223, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_205, c_74])).
% 2.89/1.45  tff(c_301, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.89/1.45  tff(c_409, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_406, c_301])).
% 2.89/1.45  tff(c_420, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_6, c_8, c_409])).
% 2.89/1.45  tff(c_426, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_420])).
% 2.89/1.45  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_426])).
% 2.89/1.45  tff(c_431, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_223])).
% 2.89/1.45  tff(c_751, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_745, c_431])).
% 2.89/1.45  tff(c_765, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_6, c_710, c_751])).
% 2.89/1.45  tff(c_771, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_765])).
% 2.89/1.45  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_771])).
% 2.89/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  Inference rules
% 2.89/1.45  ----------------------
% 2.89/1.45  #Ref     : 0
% 2.89/1.45  #Sup     : 166
% 2.89/1.45  #Fact    : 0
% 2.89/1.45  #Define  : 0
% 2.89/1.45  #Split   : 3
% 2.89/1.45  #Chain   : 0
% 2.89/1.45  #Close   : 0
% 2.89/1.45  
% 2.89/1.45  Ordering : KBO
% 2.89/1.45  
% 2.89/1.45  Simplification rules
% 2.89/1.45  ----------------------
% 2.89/1.45  #Subsume      : 6
% 2.89/1.45  #Demod        : 52
% 2.89/1.45  #Tautology    : 69
% 2.89/1.45  #SimpNegUnit  : 0
% 2.89/1.45  #BackRed      : 0
% 2.89/1.45  
% 2.89/1.45  #Partial instantiations: 0
% 2.89/1.45  #Strategies tried      : 1
% 2.89/1.45  
% 2.89/1.45  Timing (in seconds)
% 2.89/1.45  ----------------------
% 2.89/1.46  Preprocessing        : 0.34
% 2.89/1.46  Parsing              : 0.17
% 2.89/1.46  CNF conversion       : 0.03
% 2.89/1.46  Main loop            : 0.35
% 2.89/1.46  Inferencing          : 0.12
% 2.89/1.46  Reduction            : 0.10
% 2.89/1.46  Demodulation         : 0.07
% 2.89/1.46  BG Simplification    : 0.02
% 2.89/1.46  Subsumption          : 0.08
% 2.89/1.46  Abstraction          : 0.03
% 2.89/1.46  MUC search           : 0.00
% 2.89/1.46  Cooper               : 0.00
% 2.89/1.46  Total                : 0.72
% 2.89/1.46  Index Insertion      : 0.00
% 2.89/1.46  Index Deletion       : 0.00
% 2.89/1.46  Index Matching       : 0.00
% 2.89/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
