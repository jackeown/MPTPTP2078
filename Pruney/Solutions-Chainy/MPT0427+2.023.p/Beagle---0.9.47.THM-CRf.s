%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 229 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 478 expanded)
%              Number of equality atoms :   41 ( 188 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_156,plain,(
    ! [A_52,B_53] :
      ( k6_setfam_1(A_52,B_53) = k1_setfam_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_168,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_257,plain,(
    ! [A_64,B_65] :
      ( k8_setfam_1(A_64,B_65) = k6_setfam_1(A_64,B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_268,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_257])).

tff(c_275,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_268])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_169,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_156])).

tff(c_271,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_257])).

tff(c_277,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_271])).

tff(c_343,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_277])).

tff(c_344,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_347,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_93])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_347])).

tff(c_355,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_244,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k8_setfam_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_380,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k8_setfam_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(resolution,[status(thm)],[c_244,c_32])).

tff(c_390,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_396,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_390])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    ! [C_47] : ~ r2_hidden(C_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_123,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_126,plain,(
    ! [A_48] :
      ( k8_setfam_1(A_48,k1_xboole_0) = A_48
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_130,plain,(
    ! [A_48] :
      ( k8_setfam_1(A_48,k1_xboole_0) = A_48
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_34,c_126])).

tff(c_192,plain,(
    ! [A_48] : k8_setfam_1(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_130])).

tff(c_282,plain,(
    ! [A_48] : k8_setfam_1(A_48,'#skF_4') = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_192])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_358,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_38])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_355,c_358])).

tff(c_403,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_404,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_413,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_123])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_93])).

tff(c_444,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_402,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_446,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_38])).

tff(c_469,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_446])).

tff(c_472,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_469])).

tff(c_475,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_472])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_475])).

tff(c_478,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_480,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_38])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.56/1.34  
% 2.56/1.34  %Foreground sorts:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Background operators:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Foreground operators:
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.34  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.56/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.34  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.56/1.34  
% 2.56/1.35  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.35  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.56/1.35  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.56/1.35  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.56/1.35  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.56/1.35  tff(f_91, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.56/1.35  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.56/1.35  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.56/1.35  tff(f_97, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.56/1.35  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.35  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.56/1.35  tff(c_156, plain, (![A_52, B_53]: (k6_setfam_1(A_52, B_53)=k1_setfam_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.35  tff(c_168, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_156])).
% 2.56/1.35  tff(c_257, plain, (![A_64, B_65]: (k8_setfam_1(A_64, B_65)=k6_setfam_1(A_64, B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.56/1.35  tff(c_268, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_257])).
% 2.56/1.35  tff(c_275, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_268])).
% 2.56/1.35  tff(c_278, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_275])).
% 2.56/1.35  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.56/1.35  tff(c_169, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_156])).
% 2.56/1.35  tff(c_271, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_257])).
% 2.56/1.35  tff(c_277, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_271])).
% 2.56/1.35  tff(c_343, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_277])).
% 2.56/1.35  tff(c_344, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_343])).
% 2.56/1.35  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.56/1.35  tff(c_70, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.35  tff(c_85, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_70])).
% 2.56/1.35  tff(c_93, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_85])).
% 2.56/1.35  tff(c_347, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_93])).
% 2.56/1.35  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_347])).
% 2.56/1.35  tff(c_355, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_343])).
% 2.56/1.35  tff(c_244, plain, (![A_62, B_63]: (m1_subset_1(k8_setfam_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.35  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.56/1.35  tff(c_380, plain, (![A_72, B_73]: (r1_tarski(k8_setfam_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(resolution, [status(thm)], [c_244, c_32])).
% 2.56/1.35  tff(c_390, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_42, c_380])).
% 2.56/1.35  tff(c_396, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_390])).
% 2.56/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.35  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.56/1.35  tff(c_106, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.56/1.35  tff(c_110, plain, (![C_47]: (~r2_hidden(C_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.56/1.35  tff(c_123, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.56/1.35  tff(c_34, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.56/1.35  tff(c_126, plain, (![A_48]: (k8_setfam_1(A_48, k1_xboole_0)=A_48 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.56/1.35  tff(c_130, plain, (![A_48]: (k8_setfam_1(A_48, k1_xboole_0)=A_48 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_34, c_126])).
% 2.56/1.35  tff(c_192, plain, (![A_48]: (k8_setfam_1(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_130])).
% 2.56/1.35  tff(c_282, plain, (![A_48]: (k8_setfam_1(A_48, '#skF_4')=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_278, c_192])).
% 2.56/1.35  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.56/1.35  tff(c_358, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_38])).
% 2.56/1.35  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_396, c_355, c_358])).
% 2.56/1.35  tff(c_403, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_275])).
% 2.56/1.35  tff(c_36, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.56/1.35  tff(c_404, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_277])).
% 2.56/1.35  tff(c_413, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_123])).
% 2.56/1.35  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_93])).
% 2.56/1.35  tff(c_444, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_277])).
% 2.56/1.35  tff(c_402, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_275])).
% 2.56/1.35  tff(c_446, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_402, c_38])).
% 2.56/1.35  tff(c_469, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_446])).
% 2.56/1.35  tff(c_472, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_469])).
% 2.56/1.35  tff(c_475, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_472])).
% 2.56/1.35  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_475])).
% 2.56/1.35  tff(c_478, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_85])).
% 2.56/1.35  tff(c_480, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_38])).
% 2.56/1.35  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_480])).
% 2.56/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  Inference rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Ref     : 0
% 2.56/1.35  #Sup     : 85
% 2.56/1.35  #Fact    : 0
% 2.56/1.35  #Define  : 0
% 2.56/1.35  #Split   : 6
% 2.56/1.35  #Chain   : 0
% 2.56/1.35  #Close   : 0
% 2.56/1.35  
% 2.56/1.35  Ordering : KBO
% 2.56/1.35  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 6
% 2.56/1.35  #Demod        : 69
% 2.56/1.35  #Tautology    : 45
% 2.56/1.35  #SimpNegUnit  : 1
% 2.56/1.35  #BackRed      : 34
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.36  Preprocessing        : 0.32
% 2.56/1.36  Parsing              : 0.17
% 2.56/1.36  CNF conversion       : 0.02
% 2.56/1.36  Main loop            : 0.26
% 2.56/1.36  Inferencing          : 0.09
% 2.56/1.36  Reduction            : 0.08
% 2.56/1.36  Demodulation         : 0.06
% 2.56/1.36  BG Simplification    : 0.02
% 2.56/1.36  Subsumption          : 0.05
% 2.56/1.36  Abstraction          : 0.02
% 2.56/1.36  MUC search           : 0.00
% 2.56/1.36  Cooper               : 0.00
% 2.56/1.36  Total                : 0.62
% 2.56/1.36  Index Insertion      : 0.00
% 2.56/1.36  Index Deletion       : 0.00
% 2.56/1.36  Index Matching       : 0.00
% 2.56/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
