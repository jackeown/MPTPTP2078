%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  101 ( 197 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_29,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_12,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_461,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,k9_relat_1(B_51,k1_relat_1(B_51))) = k9_relat_1(B_51,k10_relat_1(B_51,A_50))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_tarski(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_23,C_24] : r1_tarski(k3_xboole_0(B_23,C_24),B_23) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [B_23,C_24] : k3_xboole_0(k3_xboole_0(B_23,C_24),B_23) = k3_xboole_0(B_23,C_24) ),
    inference(resolution,[status(thm)],[c_74,c_10])).

tff(c_1568,plain,(
    ! [B_110,A_111] :
      ( k3_xboole_0(k9_relat_1(B_110,k10_relat_1(B_110,A_111)),A_111) = k3_xboole_0(A_111,k9_relat_1(B_110,k1_relat_1(B_110)))
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_92])).

tff(c_73,plain,(
    ! [B_21,C_22] : r1_tarski(k3_xboole_0(B_21,C_22),B_21) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_1660,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(k3_xboole_0(A_112,k9_relat_1(B_113,k1_relat_1(B_113))),k9_relat_1(B_113,k10_relat_1(B_113,A_112)))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_73])).

tff(c_1714,plain,(
    ! [A_114,A_115] :
      ( r1_tarski(k3_xboole_0(A_114,k2_relat_1(A_115)),k9_relat_1(A_115,k10_relat_1(A_115,A_114)))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1660])).

tff(c_1754,plain,
    ( r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1714])).

tff(c_1767,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_24,c_1754])).

tff(c_556,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k9_relat_1(B_52,k10_relat_1(B_52,A_53)),A_53)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_73])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_566,plain,(
    ! [B_52,A_53] :
      ( k9_relat_1(B_52,k10_relat_1(B_52,A_53)) = A_53
      | ~ r1_tarski(A_53,k9_relat_1(B_52,k10_relat_1(B_52,A_53)))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_556,c_2])).

tff(c_1770,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1767,c_566])).

tff(c_1784,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1770])).

tff(c_14,plain,(
    ! [C_11,A_9,D_13,B_10] :
      ( r1_tarski(k9_relat_1(C_11,A_9),k9_relat_1(D_13,B_10))
      | ~ r1_tarski(A_9,B_10)
      | ~ r1_tarski(C_11,D_13)
      | ~ v1_relat_1(D_13)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1827,plain,(
    ! [D_13,B_10] :
      ( r1_tarski('#skF_1',k9_relat_1(D_13,B_10))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_10)
      | ~ r1_tarski('#skF_3',D_13)
      | ~ v1_relat_1(D_13)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_14])).

tff(c_2326,plain,(
    ! [D_127,B_128] :
      ( r1_tarski('#skF_1',k9_relat_1(D_127,B_128))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_128)
      | ~ r1_tarski('#skF_3',D_127)
      | ~ v1_relat_1(D_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1827])).

tff(c_2402,plain,(
    ! [D_133] :
      ( r1_tarski('#skF_1',k9_relat_1(D_133,k10_relat_1('#skF_3','#skF_2')))
      | ~ r1_tarski('#skF_3',D_133)
      | ~ v1_relat_1(D_133) ) ),
    inference(resolution,[status(thm)],[c_22,c_2326])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_531,plain,(
    ! [A_3,A_50,B_51] :
      ( r1_tarski(A_3,A_50)
      | ~ r1_tarski(A_3,k9_relat_1(B_51,k10_relat_1(B_51,A_50)))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_8])).

tff(c_2406,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2402,c_531])).

tff(c_2418,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_24,c_2406])).

tff(c_2420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:19:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.69  
% 3.93/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.69  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.93/1.69  
% 3.93/1.69  %Foreground sorts:
% 3.93/1.69  
% 3.93/1.69  
% 3.93/1.69  %Background operators:
% 3.93/1.69  
% 3.93/1.69  
% 3.93/1.69  %Foreground operators:
% 3.93/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.93/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.93/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.93/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.93/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.69  
% 3.93/1.71  tff(f_71, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 3.93/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.93/1.71  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.93/1.71  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.93/1.71  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 3.93/1.71  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.93/1.71  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 3.93/1.71  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.71  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.71  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.71  tff(c_22, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.71  tff(c_20, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.71  tff(c_29, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.93/1.71  tff(c_36, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_29])).
% 3.93/1.71  tff(c_12, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.93/1.71  tff(c_461, plain, (![A_50, B_51]: (k3_xboole_0(A_50, k9_relat_1(B_51, k1_relat_1(B_51)))=k9_relat_1(B_51, k10_relat_1(B_51, A_50)) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.93/1.71  tff(c_59, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, B_21) | ~r1_tarski(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.93/1.71  tff(c_74, plain, (![B_23, C_24]: (r1_tarski(k3_xboole_0(B_23, C_24), B_23))), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.93/1.71  tff(c_10, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.93/1.71  tff(c_92, plain, (![B_23, C_24]: (k3_xboole_0(k3_xboole_0(B_23, C_24), B_23)=k3_xboole_0(B_23, C_24))), inference(resolution, [status(thm)], [c_74, c_10])).
% 3.93/1.71  tff(c_1568, plain, (![B_110, A_111]: (k3_xboole_0(k9_relat_1(B_110, k10_relat_1(B_110, A_111)), A_111)=k3_xboole_0(A_111, k9_relat_1(B_110, k1_relat_1(B_110))) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_461, c_92])).
% 3.93/1.71  tff(c_73, plain, (![B_21, C_22]: (r1_tarski(k3_xboole_0(B_21, C_22), B_21))), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.93/1.71  tff(c_1660, plain, (![A_112, B_113]: (r1_tarski(k3_xboole_0(A_112, k9_relat_1(B_113, k1_relat_1(B_113))), k9_relat_1(B_113, k10_relat_1(B_113, A_112))) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_1568, c_73])).
% 3.93/1.71  tff(c_1714, plain, (![A_114, A_115]: (r1_tarski(k3_xboole_0(A_114, k2_relat_1(A_115)), k9_relat_1(A_115, k10_relat_1(A_115, A_114))) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1660])).
% 3.93/1.71  tff(c_1754, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1714])).
% 3.93/1.71  tff(c_1767, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_24, c_1754])).
% 3.93/1.71  tff(c_556, plain, (![B_52, A_53]: (r1_tarski(k9_relat_1(B_52, k10_relat_1(B_52, A_53)), A_53) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_461, c_73])).
% 3.93/1.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.71  tff(c_566, plain, (![B_52, A_53]: (k9_relat_1(B_52, k10_relat_1(B_52, A_53))=A_53 | ~r1_tarski(A_53, k9_relat_1(B_52, k10_relat_1(B_52, A_53))) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_556, c_2])).
% 3.93/1.71  tff(c_1770, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1767, c_566])).
% 3.93/1.71  tff(c_1784, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1770])).
% 3.93/1.71  tff(c_14, plain, (![C_11, A_9, D_13, B_10]: (r1_tarski(k9_relat_1(C_11, A_9), k9_relat_1(D_13, B_10)) | ~r1_tarski(A_9, B_10) | ~r1_tarski(C_11, D_13) | ~v1_relat_1(D_13) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.93/1.71  tff(c_1827, plain, (![D_13, B_10]: (r1_tarski('#skF_1', k9_relat_1(D_13, B_10)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_10) | ~r1_tarski('#skF_3', D_13) | ~v1_relat_1(D_13) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1784, c_14])).
% 3.93/1.71  tff(c_2326, plain, (![D_127, B_128]: (r1_tarski('#skF_1', k9_relat_1(D_127, B_128)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_128) | ~r1_tarski('#skF_3', D_127) | ~v1_relat_1(D_127))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1827])).
% 3.93/1.71  tff(c_2402, plain, (![D_133]: (r1_tarski('#skF_1', k9_relat_1(D_133, k10_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski('#skF_3', D_133) | ~v1_relat_1(D_133))), inference(resolution, [status(thm)], [c_22, c_2326])).
% 3.93/1.71  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.93/1.71  tff(c_531, plain, (![A_3, A_50, B_51]: (r1_tarski(A_3, A_50) | ~r1_tarski(A_3, k9_relat_1(B_51, k10_relat_1(B_51, A_50))) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_461, c_8])).
% 3.93/1.71  tff(c_2406, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2402, c_531])).
% 3.93/1.71  tff(c_2418, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_24, c_2406])).
% 3.93/1.71  tff(c_2420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_2418])).
% 3.93/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.71  
% 3.93/1.71  Inference rules
% 3.93/1.71  ----------------------
% 3.93/1.71  #Ref     : 0
% 3.93/1.71  #Sup     : 596
% 3.93/1.71  #Fact    : 0
% 3.93/1.71  #Define  : 0
% 3.93/1.71  #Split   : 2
% 3.93/1.71  #Chain   : 0
% 3.93/1.71  #Close   : 0
% 3.93/1.71  
% 3.93/1.71  Ordering : KBO
% 3.93/1.71  
% 3.93/1.71  Simplification rules
% 3.93/1.71  ----------------------
% 3.93/1.71  #Subsume      : 87
% 3.93/1.71  #Demod        : 377
% 3.93/1.71  #Tautology    : 272
% 3.93/1.71  #SimpNegUnit  : 1
% 3.93/1.71  #BackRed      : 1
% 3.93/1.71  
% 3.93/1.71  #Partial instantiations: 0
% 3.93/1.71  #Strategies tried      : 1
% 3.93/1.71  
% 3.93/1.71  Timing (in seconds)
% 3.93/1.71  ----------------------
% 3.93/1.71  Preprocessing        : 0.28
% 3.93/1.71  Parsing              : 0.16
% 3.93/1.71  CNF conversion       : 0.02
% 3.93/1.71  Main loop            : 0.64
% 3.93/1.71  Inferencing          : 0.24
% 3.93/1.71  Reduction            : 0.22
% 3.93/1.71  Demodulation         : 0.17
% 3.93/1.71  BG Simplification    : 0.03
% 3.93/1.71  Subsumption          : 0.11
% 3.93/1.71  Abstraction          : 0.04
% 3.93/1.71  MUC search           : 0.00
% 3.93/1.71  Cooper               : 0.00
% 3.93/1.71  Total                : 0.94
% 3.93/1.71  Index Insertion      : 0.00
% 3.93/1.71  Index Deletion       : 0.00
% 3.93/1.71  Index Matching       : 0.00
% 3.93/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
