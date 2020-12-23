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
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :   88 ( 116 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_44,plain,(
    ~ r1_setfam_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_5'(A_24,B_25),A_24)
      | r1_setfam_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_22] : k3_tarski(k1_zfmisc_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [C_53,A_54,D_55] :
      ( r2_hidden(C_53,k3_tarski(A_54))
      | ~ r2_hidden(D_55,A_54)
      | ~ r2_hidden(C_53,D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,k3_tarski(B_81))
      | ~ r2_hidden(C_80,A_82)
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_268,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden(A_95,k3_tarski(B_96))
      | v1_xboole_0(B_96)
      | ~ m1_subset_1(B_97,B_96)
      | v1_xboole_0(B_97)
      | ~ m1_subset_1(A_95,B_97) ) ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_270,plain,(
    ! [A_95,B_39,A_38] :
      ( r2_hidden(A_95,k3_tarski(k1_zfmisc_1(B_39)))
      | v1_xboole_0(k1_zfmisc_1(B_39))
      | v1_xboole_0(A_38)
      | ~ m1_subset_1(A_95,A_38)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_42,c_268])).

tff(c_272,plain,(
    ! [A_95,B_39,A_38] :
      ( r2_hidden(A_95,B_39)
      | v1_xboole_0(k1_zfmisc_1(B_39))
      | v1_xboole_0(A_38)
      | ~ m1_subset_1(A_95,A_38)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_270])).

tff(c_274,plain,(
    ! [A_98,B_99,A_100] :
      ( r2_hidden(A_98,B_99)
      | v1_xboole_0(A_100)
      | ~ m1_subset_1(A_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_272])).

tff(c_276,plain,(
    ! [A_38,B_99,B_39] :
      ( r2_hidden(A_38,B_99)
      | v1_xboole_0(k1_zfmisc_1(B_39))
      | ~ r1_tarski(k1_zfmisc_1(B_39),B_99)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_42,c_274])).

tff(c_280,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden(A_101,B_102)
      | ~ r1_tarski(k1_zfmisc_1(B_103),B_102)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_276])).

tff(c_289,plain,(
    ! [A_104,B_105] :
      ( r2_hidden(A_104,k1_zfmisc_1(B_105))
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_280])).

tff(c_8,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k3_tarski(A_3))
      | ~ r2_hidden(D_21,A_3)
      | ~ r2_hidden(C_18,D_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_297,plain,(
    ! [C_18,B_105,A_104] :
      ( r2_hidden(C_18,k3_tarski(k1_zfmisc_1(B_105)))
      | ~ r2_hidden(C_18,A_104)
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_302,plain,(
    ! [C_106,B_107,A_108] :
      ( r2_hidden(C_106,B_107)
      | ~ r2_hidden(C_106,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_297])).

tff(c_348,plain,(
    ! [A_112,B_113,B_114] :
      ( r2_hidden('#skF_5'(A_112,B_113),B_114)
      | ~ r1_tarski(A_112,B_114)
      | r1_setfam_1(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_36,c_302])).

tff(c_101,plain,(
    ! [A_60,B_61,D_62] :
      ( ~ r1_tarski('#skF_5'(A_60,B_61),D_62)
      | ~ r2_hidden(D_62,B_61)
      | r1_setfam_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden('#skF_5'(A_60,B_61),B_61)
      | r1_setfam_1(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_372,plain,(
    ! [A_115,B_116] :
      ( ~ r1_tarski(A_115,B_116)
      | r1_setfam_1(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_348,c_106])).

tff(c_381,plain,(
    r1_setfam_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_372])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.22/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.22/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.31  
% 2.22/1.32  tff(f_73, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.22/1.32  tff(f_58, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.22/1.32  tff(f_43, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.22/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.32  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.22/1.32  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.32  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.22/1.32  tff(f_41, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.22/1.32  tff(c_44, plain, (~r1_setfam_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.32  tff(c_46, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.32  tff(c_36, plain, (![A_24, B_25]: (r2_hidden('#skF_5'(A_24, B_25), A_24) | r1_setfam_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.32  tff(c_26, plain, (![A_22]: (k3_tarski(k1_zfmisc_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.32  tff(c_28, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.32  tff(c_42, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.32  tff(c_38, plain, (![A_36, B_37]: (r2_hidden(A_36, B_37) | v1_xboole_0(B_37) | ~m1_subset_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.32  tff(c_78, plain, (![C_53, A_54, D_55]: (r2_hidden(C_53, k3_tarski(A_54)) | ~r2_hidden(D_55, A_54) | ~r2_hidden(C_53, D_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.32  tff(c_150, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, k3_tarski(B_81)) | ~r2_hidden(C_80, A_82) | v1_xboole_0(B_81) | ~m1_subset_1(A_82, B_81))), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.22/1.32  tff(c_268, plain, (![A_95, B_96, B_97]: (r2_hidden(A_95, k3_tarski(B_96)) | v1_xboole_0(B_96) | ~m1_subset_1(B_97, B_96) | v1_xboole_0(B_97) | ~m1_subset_1(A_95, B_97))), inference(resolution, [status(thm)], [c_38, c_150])).
% 2.22/1.32  tff(c_270, plain, (![A_95, B_39, A_38]: (r2_hidden(A_95, k3_tarski(k1_zfmisc_1(B_39))) | v1_xboole_0(k1_zfmisc_1(B_39)) | v1_xboole_0(A_38) | ~m1_subset_1(A_95, A_38) | ~r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_42, c_268])).
% 2.22/1.32  tff(c_272, plain, (![A_95, B_39, A_38]: (r2_hidden(A_95, B_39) | v1_xboole_0(k1_zfmisc_1(B_39)) | v1_xboole_0(A_38) | ~m1_subset_1(A_95, A_38) | ~r1_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_270])).
% 2.22/1.32  tff(c_274, plain, (![A_98, B_99, A_100]: (r2_hidden(A_98, B_99) | v1_xboole_0(A_100) | ~m1_subset_1(A_98, A_100) | ~r1_tarski(A_100, B_99))), inference(negUnitSimplification, [status(thm)], [c_28, c_272])).
% 2.22/1.32  tff(c_276, plain, (![A_38, B_99, B_39]: (r2_hidden(A_38, B_99) | v1_xboole_0(k1_zfmisc_1(B_39)) | ~r1_tarski(k1_zfmisc_1(B_39), B_99) | ~r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_42, c_274])).
% 2.22/1.32  tff(c_280, plain, (![A_101, B_102, B_103]: (r2_hidden(A_101, B_102) | ~r1_tarski(k1_zfmisc_1(B_103), B_102) | ~r1_tarski(A_101, B_103))), inference(negUnitSimplification, [status(thm)], [c_28, c_276])).
% 2.22/1.32  tff(c_289, plain, (![A_104, B_105]: (r2_hidden(A_104, k1_zfmisc_1(B_105)) | ~r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_6, c_280])).
% 2.22/1.32  tff(c_8, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k3_tarski(A_3)) | ~r2_hidden(D_21, A_3) | ~r2_hidden(C_18, D_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.32  tff(c_297, plain, (![C_18, B_105, A_104]: (r2_hidden(C_18, k3_tarski(k1_zfmisc_1(B_105))) | ~r2_hidden(C_18, A_104) | ~r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_289, c_8])).
% 2.22/1.32  tff(c_302, plain, (![C_106, B_107, A_108]: (r2_hidden(C_106, B_107) | ~r2_hidden(C_106, A_108) | ~r1_tarski(A_108, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_297])).
% 2.22/1.32  tff(c_348, plain, (![A_112, B_113, B_114]: (r2_hidden('#skF_5'(A_112, B_113), B_114) | ~r1_tarski(A_112, B_114) | r1_setfam_1(A_112, B_113))), inference(resolution, [status(thm)], [c_36, c_302])).
% 2.22/1.32  tff(c_101, plain, (![A_60, B_61, D_62]: (~r1_tarski('#skF_5'(A_60, B_61), D_62) | ~r2_hidden(D_62, B_61) | r1_setfam_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.32  tff(c_106, plain, (![A_60, B_61]: (~r2_hidden('#skF_5'(A_60, B_61), B_61) | r1_setfam_1(A_60, B_61))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.22/1.32  tff(c_372, plain, (![A_115, B_116]: (~r1_tarski(A_115, B_116) | r1_setfam_1(A_115, B_116))), inference(resolution, [status(thm)], [c_348, c_106])).
% 2.22/1.32  tff(c_381, plain, (r1_setfam_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_46, c_372])).
% 2.22/1.32  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_381])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 80
% 2.22/1.32  #Fact    : 0
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 1
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 3
% 2.22/1.32  #Demod        : 8
% 2.22/1.32  #Tautology    : 7
% 2.22/1.32  #SimpNegUnit  : 4
% 2.22/1.32  #BackRed      : 0
% 2.22/1.32  
% 2.22/1.32  #Partial instantiations: 0
% 2.22/1.32  #Strategies tried      : 1
% 2.22/1.32  
% 2.22/1.32  Timing (in seconds)
% 2.22/1.32  ----------------------
% 2.22/1.32  Preprocessing        : 0.29
% 2.22/1.32  Parsing              : 0.15
% 2.22/1.32  CNF conversion       : 0.02
% 2.22/1.32  Main loop            : 0.26
% 2.22/1.33  Inferencing          : 0.10
% 2.22/1.33  Reduction            : 0.06
% 2.22/1.33  Demodulation         : 0.04
% 2.22/1.33  BG Simplification    : 0.02
% 2.22/1.33  Subsumption          : 0.06
% 2.22/1.33  Abstraction          : 0.01
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.58
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
