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
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 216 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 780 expanded)
%              Number of equality atoms :   32 ( 214 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    ! [D_33,C_34,B_35,A_36] :
      ( k1_funct_1(k2_funct_1(D_33),k1_funct_1(D_33,C_34)) = C_34
      | k1_xboole_0 = B_35
      | ~ r2_hidden(C_34,A_36)
      | ~ v2_funct_1(D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_36,B_35)))
      | ~ v1_funct_2(D_33,A_36,B_35)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [D_37,B_38] :
      ( k1_funct_1(k2_funct_1(D_37),k1_funct_1(D_37,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_38
      | ~ v2_funct_1(D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_38)))
      | ~ v1_funct_2(D_37,'#skF_1',B_38)
      | ~ v1_funct_1(D_37) ) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_116,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_120,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_116])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_8])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [A_24,C_25,B_26] :
      ( m1_subset_1(A_24,C_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_28,B_29,A_30] :
      ( m1_subset_1(A_28,B_29)
      | ~ r2_hidden(A_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_89,plain,(
    ! [B_29] :
      ( m1_subset_1('#skF_4',B_29)
      | ~ r1_tarski('#skF_1',B_29) ) ),
    inference(resolution,[status(thm)],[c_22,c_84])).

tff(c_166,plain,(
    ! [B_43] : m1_subset_1('#skF_4',B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_89])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [B_5] : r1_tarski('#skF_4',B_5) ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_50,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(B_21,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_188,plain,(
    ! [A_46] :
      ( A_46 = '#skF_1'
      | ~ r1_tarski(A_46,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_62])).

tff(c_205,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_179,c_188])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,(
    ! [B_29] :
      ( m1_subset_1('#skF_3',B_29)
      | ~ r1_tarski('#skF_1',B_29) ) ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_151,plain,(
    ! [B_42] : m1_subset_1('#skF_3',B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_90])).

tff(c_164,plain,(
    ! [B_5] : r1_tarski('#skF_3',B_5) ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_206,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_164,c_188])).

tff(c_252,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_206])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_252])).

tff(c_254,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_255,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_20,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_256,plain,(
    ! [D_49,B_50] :
      ( k1_funct_1(k2_funct_1(D_49),k1_funct_1(D_49,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_50
      | ~ v2_funct_1(D_49)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_50)))
      | ~ v1_funct_2(D_49,'#skF_1',B_50)
      | ~ v1_funct_1(D_49) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_261,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_256])).

tff(c_265,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_20,c_261])).

tff(c_266,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_265])).

tff(c_271,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_266])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:31:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.30  
% 1.90/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.90/1.30  
% 1.90/1.30  %Foreground sorts:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Background operators:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Foreground operators:
% 1.90/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.90/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.30  
% 2.18/1.32  tff(f_75, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.18/1.32  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.18/1.32  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.18/1.32  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.32  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.18/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.32  tff(c_18, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_30, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_26, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_104, plain, (![D_33, C_34, B_35, A_36]: (k1_funct_1(k2_funct_1(D_33), k1_funct_1(D_33, C_34))=C_34 | k1_xboole_0=B_35 | ~r2_hidden(C_34, A_36) | ~v2_funct_1(D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_36, B_35))) | ~v1_funct_2(D_33, A_36, B_35) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.32  tff(c_111, plain, (![D_37, B_38]: (k1_funct_1(k2_funct_1(D_37), k1_funct_1(D_37, '#skF_4'))='#skF_4' | k1_xboole_0=B_38 | ~v2_funct_1(D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_38))) | ~v1_funct_2(D_37, '#skF_1', B_38) | ~v1_funct_1(D_37))), inference(resolution, [status(thm)], [c_22, c_104])).
% 2.18/1.32  tff(c_116, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_111])).
% 2.18/1.32  tff(c_120, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_116])).
% 2.18/1.32  tff(c_121, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_120])).
% 2.18/1.32  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.32  tff(c_125, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_8])).
% 2.18/1.32  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.32  tff(c_76, plain, (![A_24, C_25, B_26]: (m1_subset_1(A_24, C_25) | ~m1_subset_1(B_26, k1_zfmisc_1(C_25)) | ~r2_hidden(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.32  tff(c_84, plain, (![A_28, B_29, A_30]: (m1_subset_1(A_28, B_29) | ~r2_hidden(A_28, A_30) | ~r1_tarski(A_30, B_29))), inference(resolution, [status(thm)], [c_12, c_76])).
% 2.18/1.32  tff(c_89, plain, (![B_29]: (m1_subset_1('#skF_4', B_29) | ~r1_tarski('#skF_1', B_29))), inference(resolution, [status(thm)], [c_22, c_84])).
% 2.18/1.32  tff(c_166, plain, (![B_43]: (m1_subset_1('#skF_4', B_43))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_89])).
% 2.18/1.32  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.32  tff(c_179, plain, (![B_5]: (r1_tarski('#skF_4', B_5))), inference(resolution, [status(thm)], [c_166, c_10])).
% 2.18/1.32  tff(c_50, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.32  tff(c_62, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_50])).
% 2.18/1.32  tff(c_188, plain, (![A_46]: (A_46='#skF_1' | ~r1_tarski(A_46, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_62])).
% 2.18/1.32  tff(c_205, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_179, c_188])).
% 2.18/1.32  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_90, plain, (![B_29]: (m1_subset_1('#skF_3', B_29) | ~r1_tarski('#skF_1', B_29))), inference(resolution, [status(thm)], [c_24, c_84])).
% 2.18/1.32  tff(c_151, plain, (![B_42]: (m1_subset_1('#skF_3', B_42))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_90])).
% 2.18/1.32  tff(c_164, plain, (![B_5]: (r1_tarski('#skF_3', B_5))), inference(resolution, [status(thm)], [c_151, c_10])).
% 2.18/1.32  tff(c_206, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_164, c_188])).
% 2.18/1.32  tff(c_252, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_206])).
% 2.18/1.32  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_252])).
% 2.18/1.32  tff(c_254, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 2.18/1.32  tff(c_255, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_120])).
% 2.18/1.32  tff(c_20, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.32  tff(c_256, plain, (![D_49, B_50]: (k1_funct_1(k2_funct_1(D_49), k1_funct_1(D_49, '#skF_3'))='#skF_3' | k1_xboole_0=B_50 | ~v2_funct_1(D_49) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_50))) | ~v1_funct_2(D_49, '#skF_1', B_50) | ~v1_funct_1(D_49))), inference(resolution, [status(thm)], [c_24, c_104])).
% 2.18/1.32  tff(c_261, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_256])).
% 2.18/1.32  tff(c_265, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_20, c_261])).
% 2.18/1.32  tff(c_266, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_255, c_265])).
% 2.18/1.32  tff(c_271, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_266])).
% 2.18/1.32  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_271])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 47
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 2
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 0
% 2.18/1.32  #Demod        : 52
% 2.18/1.32  #Tautology    : 20
% 2.18/1.32  #SimpNegUnit  : 3
% 2.18/1.32  #BackRed      : 18
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.18/1.32  Preprocessing        : 0.28
% 2.18/1.32  Parsing              : 0.15
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.20
% 2.18/1.32  Inferencing          : 0.07
% 2.18/1.32  Reduction            : 0.07
% 2.18/1.32  Demodulation         : 0.05
% 2.18/1.32  BG Simplification    : 0.01
% 2.18/1.32  Subsumption          : 0.04
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.52
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
