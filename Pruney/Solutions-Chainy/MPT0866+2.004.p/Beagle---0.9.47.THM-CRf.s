%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  83 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_241,plain,(
    ! [A_90,B_91] :
      ( k4_tarski(k1_mcart_1(A_90),k2_mcart_1(A_90)) = A_90
      | ~ r2_hidden(A_90,B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [A_100,B_101] :
      ( k4_tarski(k1_mcart_1(A_100),k2_mcart_1(A_100)) = A_100
      | ~ v1_relat_1(B_101)
      | v1_xboole_0(B_101)
      | ~ m1_subset_1(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_256,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_254])).

tff(c_259,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_256])).

tff(c_260,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_259])).

tff(c_188,plain,(
    ! [A_70,B_71] :
      ( k1_relat_1(k2_zfmisc_1(A_70,B_71)) = A_70
      | k1_xboole_0 = B_71
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7] :
      ( v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_197,plain,(
    ! [A_70,B_71] :
      ( v1_xboole_0(A_70)
      | ~ v1_xboole_0(k2_zfmisc_1(A_70,B_71))
      | k1_xboole_0 = B_71
      | k1_xboole_0 = A_70 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_8])).

tff(c_266,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_260,c_197])).

tff(c_278,plain,(
    v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_266])).

tff(c_34,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_2'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_286,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_278,c_38])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  
% 2.32/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.32/1.26  
% 2.32/1.26  %Foreground sorts:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Background operators:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Foreground operators:
% 2.32/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.32/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.32/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.26  
% 2.32/1.27  tff(f_91, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.32/1.27  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.32/1.27  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.32/1.27  tff(f_55, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.32/1.27  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.32/1.27  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.32/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.27  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.32/1.27  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.32/1.27  tff(c_24, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.32/1.27  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.27  tff(c_26, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.32/1.27  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.27  tff(c_241, plain, (![A_90, B_91]: (k4_tarski(k1_mcart_1(A_90), k2_mcart_1(A_90))=A_90 | ~r2_hidden(A_90, B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.32/1.27  tff(c_254, plain, (![A_100, B_101]: (k4_tarski(k1_mcart_1(A_100), k2_mcart_1(A_100))=A_100 | ~v1_relat_1(B_101) | v1_xboole_0(B_101) | ~m1_subset_1(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_241])).
% 2.32/1.27  tff(c_256, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_254])).
% 2.32/1.27  tff(c_259, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_256])).
% 2.32/1.27  tff(c_260, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24, c_259])).
% 2.32/1.27  tff(c_188, plain, (![A_70, B_71]: (k1_relat_1(k2_zfmisc_1(A_70, B_71))=A_70 | k1_xboole_0=B_71 | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.32/1.27  tff(c_8, plain, (![A_7]: (v1_xboole_0(k1_relat_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.27  tff(c_197, plain, (![A_70, B_71]: (v1_xboole_0(A_70) | ~v1_xboole_0(k2_zfmisc_1(A_70, B_71)) | k1_xboole_0=B_71 | k1_xboole_0=A_70)), inference(superposition, [status(thm), theory('equality')], [c_188, c_8])).
% 2.32/1.27  tff(c_266, plain, (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_260, c_197])).
% 2.32/1.27  tff(c_278, plain, (v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_266])).
% 2.32/1.27  tff(c_34, plain, (![A_30]: (r2_hidden('#skF_2'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.32/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.27  tff(c_38, plain, (![A_30]: (~v1_xboole_0(A_30) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_34, c_2])).
% 2.32/1.27  tff(c_286, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_278, c_38])).
% 2.32/1.27  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_286])).
% 2.32/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  
% 2.32/1.27  Inference rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Ref     : 0
% 2.32/1.27  #Sup     : 54
% 2.32/1.27  #Fact    : 0
% 2.32/1.27  #Define  : 0
% 2.32/1.27  #Split   : 1
% 2.32/1.27  #Chain   : 0
% 2.32/1.27  #Close   : 0
% 2.32/1.27  
% 2.32/1.27  Ordering : KBO
% 2.32/1.27  
% 2.32/1.27  Simplification rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Subsume      : 9
% 2.32/1.27  #Demod        : 8
% 2.32/1.27  #Tautology    : 19
% 2.32/1.27  #SimpNegUnit  : 8
% 2.32/1.27  #BackRed      : 1
% 2.32/1.27  
% 2.32/1.27  #Partial instantiations: 0
% 2.32/1.27  #Strategies tried      : 1
% 2.32/1.27  
% 2.32/1.27  Timing (in seconds)
% 2.32/1.27  ----------------------
% 2.32/1.27  Preprocessing        : 0.28
% 2.32/1.27  Parsing              : 0.15
% 2.32/1.27  CNF conversion       : 0.02
% 2.32/1.27  Main loop            : 0.21
% 2.32/1.27  Inferencing          : 0.08
% 2.32/1.27  Reduction            : 0.05
% 2.32/1.27  Demodulation         : 0.03
% 2.32/1.27  BG Simplification    : 0.01
% 2.32/1.27  Subsumption          : 0.04
% 2.32/1.27  Abstraction          : 0.01
% 2.32/1.27  MUC search           : 0.00
% 2.32/1.27  Cooper               : 0.00
% 2.32/1.27  Total                : 0.51
% 2.32/1.27  Index Insertion      : 0.00
% 2.32/1.27  Index Deletion       : 0.00
% 2.32/1.27  Index Matching       : 0.00
% 2.32/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
