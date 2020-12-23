%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 131 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 218 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_60,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

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

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [A_85,B_86,C_87,D_88] : k3_enumset1(A_85,A_85,B_86,C_87,D_88) = k2_enumset1(A_85,B_86,C_87,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,G_23,C_17] : r2_hidden(G_23,k3_enumset1(A_15,B_16,C_17,D_18,G_23)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_207,plain,(
    ! [D_108,A_109,B_110,C_111] : r2_hidden(D_108,k2_enumset1(A_109,B_110,C_111,D_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_14])).

tff(c_214,plain,(
    ! [C_112,A_113,B_114] : r2_hidden(C_112,k1_enumset1(A_113,B_114,C_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_207])).

tff(c_219,plain,(
    ! [B_7,A_6] : r2_hidden(B_7,k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_214])).

tff(c_48,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k1_setfam_1(B_43),A_44)
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_367,plain,(
    ! [A_169,B_170,A_171] :
      ( r1_tarski(k3_xboole_0(A_169,B_170),A_171)
      | ~ r2_hidden(A_171,k2_tarski(A_169,B_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_76])).

tff(c_374,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),B_7) ),
    inference(resolution,[status(thm)],[c_219,c_367])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_264,plain,(
    ! [B_128,A_129] : r2_hidden(B_128,k2_tarski(A_129,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_214])).

tff(c_54,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_setfam_1(B_29),A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_102,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(A_66)
      | ~ v1_relat_1(B_67)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_109,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k1_setfam_1(B_29))
      | ~ v1_relat_1(A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_266,plain,(
    ! [A_129,B_128] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_129,B_128)))
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_264,c_109])).

tff(c_268,plain,(
    ! [A_129,B_128] :
      ( v1_relat_1(k3_xboole_0(A_129,B_128))
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_266])).

tff(c_288,plain,(
    ! [A_139,B_140] :
      ( r1_tarski(k3_relat_1(A_139),k3_relat_1(B_140))
      | ~ r1_tarski(A_139,B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_222,plain,(
    ! [B_115,A_116] : r2_hidden(B_115,k2_tarski(A_116,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_214])).

tff(c_224,plain,(
    ! [A_116,B_115] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_116,B_115)))
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_222,c_109])).

tff(c_226,plain,(
    ! [A_116,B_115] :
      ( v1_relat_1(k3_xboole_0(A_116,B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_224])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_241,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(k3_relat_1(A_126),k3_relat_1(B_127))
      | ~ r1_tarski(A_126,B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_197,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(A_105,k3_xboole_0(B_106,C_107))
      | ~ r1_tarski(A_105,C_107)
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_205,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_197,c_60])).

tff(c_221,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_244,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_241,c_221])).

tff(c_250,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2,c_244])).

tff(c_254,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_250])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_254])).

tff(c_262,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_291,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_288,c_262])).

tff(c_297,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_291])).

tff(c_309,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_312,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_268,c_309])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_312])).

tff(c_320,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.33  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.28/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.28/1.33  
% 2.59/1.34  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.59/1.34  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.59/1.34  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.59/1.34  tff(f_60, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.59/1.34  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.59/1.34  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.59/1.34  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.59/1.34  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.59/1.34  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.34  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.59/1.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.59/1.34  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.59/1.34  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.34  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.34  tff(c_139, plain, (![A_85, B_86, C_87, D_88]: (k3_enumset1(A_85, A_85, B_86, C_87, D_88)=k2_enumset1(A_85, B_86, C_87, D_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.34  tff(c_14, plain, (![B_16, A_15, D_18, G_23, C_17]: (r2_hidden(G_23, k3_enumset1(A_15, B_16, C_17, D_18, G_23)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.34  tff(c_207, plain, (![D_108, A_109, B_110, C_111]: (r2_hidden(D_108, k2_enumset1(A_109, B_110, C_111, D_108)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_14])).
% 2.59/1.34  tff(c_214, plain, (![C_112, A_113, B_114]: (r2_hidden(C_112, k1_enumset1(A_113, B_114, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_207])).
% 2.59/1.34  tff(c_219, plain, (![B_7, A_6]: (r2_hidden(B_7, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_214])).
% 2.59/1.34  tff(c_48, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.34  tff(c_76, plain, (![B_43, A_44]: (r1_tarski(k1_setfam_1(B_43), A_44) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.34  tff(c_367, plain, (![A_169, B_170, A_171]: (r1_tarski(k3_xboole_0(A_169, B_170), A_171) | ~r2_hidden(A_171, k2_tarski(A_169, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_76])).
% 2.59/1.34  tff(c_374, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), B_7))), inference(resolution, [status(thm)], [c_219, c_367])).
% 2.59/1.34  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.59/1.34  tff(c_264, plain, (![B_128, A_129]: (r2_hidden(B_128, k2_tarski(A_129, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_214])).
% 2.59/1.34  tff(c_54, plain, (![B_29, A_28]: (r1_tarski(k1_setfam_1(B_29), A_28) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.34  tff(c_52, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.34  tff(c_97, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.34  tff(c_102, plain, (![A_66, B_67]: (v1_relat_1(A_66) | ~v1_relat_1(B_67) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_52, c_97])).
% 2.59/1.34  tff(c_109, plain, (![B_29, A_28]: (v1_relat_1(k1_setfam_1(B_29)) | ~v1_relat_1(A_28) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_54, c_102])).
% 2.59/1.34  tff(c_266, plain, (![A_129, B_128]: (v1_relat_1(k1_setfam_1(k2_tarski(A_129, B_128))) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_264, c_109])).
% 2.59/1.34  tff(c_268, plain, (![A_129, B_128]: (v1_relat_1(k3_xboole_0(A_129, B_128)) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_266])).
% 2.59/1.34  tff(c_288, plain, (![A_139, B_140]: (r1_tarski(k3_relat_1(A_139), k3_relat_1(B_140)) | ~r1_tarski(A_139, B_140) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.59/1.34  tff(c_222, plain, (![B_115, A_116]: (r2_hidden(B_115, k2_tarski(A_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_214])).
% 2.59/1.34  tff(c_224, plain, (![A_116, B_115]: (v1_relat_1(k1_setfam_1(k2_tarski(A_116, B_115))) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_222, c_109])).
% 2.59/1.34  tff(c_226, plain, (![A_116, B_115]: (v1_relat_1(k3_xboole_0(A_116, B_115)) | ~v1_relat_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_224])).
% 2.59/1.34  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.59/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.34  tff(c_241, plain, (![A_126, B_127]: (r1_tarski(k3_relat_1(A_126), k3_relat_1(B_127)) | ~r1_tarski(A_126, B_127) | ~v1_relat_1(B_127) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.59/1.34  tff(c_197, plain, (![A_105, B_106, C_107]: (r1_tarski(A_105, k3_xboole_0(B_106, C_107)) | ~r1_tarski(A_105, C_107) | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.34  tff(c_60, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.59/1.34  tff(c_205, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_197, c_60])).
% 2.59/1.34  tff(c_221, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_205])).
% 2.59/1.34  tff(c_244, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_241, c_221])).
% 2.59/1.34  tff(c_250, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2, c_244])).
% 2.59/1.34  tff(c_254, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_226, c_250])).
% 2.59/1.34  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_254])).
% 2.59/1.34  tff(c_262, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_205])).
% 2.59/1.34  tff(c_291, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_288, c_262])).
% 2.59/1.34  tff(c_297, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_291])).
% 2.59/1.34  tff(c_309, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_297])).
% 2.59/1.34  tff(c_312, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_268, c_309])).
% 2.59/1.34  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_312])).
% 2.59/1.34  tff(c_320, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_297])).
% 2.59/1.34  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_320])).
% 2.59/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.34  
% 2.59/1.34  Inference rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Ref     : 0
% 2.59/1.34  #Sup     : 69
% 2.59/1.34  #Fact    : 0
% 2.59/1.34  #Define  : 0
% 2.59/1.34  #Split   : 3
% 2.59/1.34  #Chain   : 0
% 2.59/1.34  #Close   : 0
% 2.59/1.34  
% 2.59/1.34  Ordering : KBO
% 2.59/1.34  
% 2.59/1.34  Simplification rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Subsume      : 9
% 2.59/1.34  #Demod        : 18
% 2.59/1.34  #Tautology    : 19
% 2.59/1.34  #SimpNegUnit  : 0
% 2.59/1.34  #BackRed      : 1
% 2.59/1.34  
% 2.59/1.34  #Partial instantiations: 0
% 2.59/1.34  #Strategies tried      : 1
% 2.59/1.34  
% 2.59/1.34  Timing (in seconds)
% 2.59/1.34  ----------------------
% 2.59/1.34  Preprocessing        : 0.32
% 2.59/1.34  Parsing              : 0.16
% 2.59/1.34  CNF conversion       : 0.02
% 2.59/1.34  Main loop            : 0.26
% 2.59/1.34  Inferencing          : 0.09
% 2.59/1.34  Reduction            : 0.07
% 2.59/1.34  Demodulation         : 0.05
% 2.59/1.34  BG Simplification    : 0.02
% 2.59/1.34  Subsumption          : 0.06
% 2.59/1.34  Abstraction          : 0.02
% 2.59/1.34  MUC search           : 0.00
% 2.59/1.34  Cooper               : 0.00
% 2.59/1.34  Total                : 0.61
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
