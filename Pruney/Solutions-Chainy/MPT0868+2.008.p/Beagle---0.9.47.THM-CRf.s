%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   64 (  91 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 178 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_65,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_55,B_56] :
      ( k4_tarski(k1_mcart_1(A_55),k2_mcart_1(A_55)) = A_55
      | ~ r2_hidden(A_55,B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    ! [A_59,B_60] :
      ( k4_tarski(k1_mcart_1(A_59),k2_mcart_1(A_59)) = A_59
      | ~ v1_relat_1(B_60)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_4,c_196])).

tff(c_203,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_206,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_65,c_203])).

tff(c_207,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_206])).

tff(c_180,plain,(
    ! [A_51,B_52] :
      ( k1_relat_1(k2_zfmisc_1(A_51,B_52)) = A_51
      | k1_xboole_0 = B_52
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_relat_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [A_51,B_52] :
      ( v1_xboole_0(A_51)
      | ~ v1_xboole_0(k2_zfmisc_1(A_51,B_52))
      | k1_xboole_0 = B_52
      | k1_xboole_0 = A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_6])).

tff(c_213,plain,
    ( v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_207,c_189])).

tff(c_225,plain,(
    v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_213])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_233,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_225,c_2])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_233])).

tff(c_239,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_370,plain,(
    ! [A_82,B_83] :
      ( k4_tarski(k1_mcart_1(A_82),k2_mcart_1(A_82)) = A_82
      | ~ r2_hidden(A_82,B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_375,plain,(
    ! [A_86,B_87] :
      ( k4_tarski(k1_mcart_1(A_86),k2_mcart_1(A_86)) = A_86
      | ~ v1_relat_1(B_87)
      | v1_xboole_0(B_87)
      | ~ m1_subset_1(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_370])).

tff(c_377,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_375])).

tff(c_380,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_239,c_377])).

tff(c_381,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_380])).

tff(c_341,plain,(
    ! [A_76,B_77] :
      ( k1_relat_1(k2_zfmisc_1(A_76,B_77)) = A_76
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_350,plain,(
    ! [A_76,B_77] :
      ( v1_xboole_0(A_76)
      | ~ v1_xboole_0(k2_zfmisc_1(A_76,B_77))
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_6])).

tff(c_387,plain,
    ( v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_381,c_350])).

tff(c_399,plain,(
    v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_387])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_399,c_2])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.36  
% 2.08/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.36  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.36  
% 2.08/1.36  %Foreground sorts:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Background operators:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Foreground operators:
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.36  
% 2.08/1.37  tff(f_90, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.08/1.37  tff(f_72, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.08/1.37  tff(f_62, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.08/1.37  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.08/1.37  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.08/1.37  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.08/1.37  tff(f_53, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.08/1.37  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.08/1.37  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.08/1.37  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.08/1.37  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.08/1.37  tff(c_22, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.37  tff(c_14, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.37  tff(c_32, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14])).
% 2.08/1.37  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.37  tff(c_20, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.37  tff(c_16, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.37  tff(c_31, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 2.08/1.37  tff(c_24, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.08/1.37  tff(c_65, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.08/1.37  tff(c_26, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.08/1.37  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.37  tff(c_196, plain, (![A_55, B_56]: (k4_tarski(k1_mcart_1(A_55), k2_mcart_1(A_55))=A_55 | ~r2_hidden(A_55, B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.37  tff(c_201, plain, (![A_59, B_60]: (k4_tarski(k1_mcart_1(A_59), k2_mcart_1(A_59))=A_59 | ~v1_relat_1(B_60) | v1_xboole_0(B_60) | ~m1_subset_1(A_59, B_60))), inference(resolution, [status(thm)], [c_4, c_196])).
% 2.08/1.37  tff(c_203, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_201])).
% 2.08/1.37  tff(c_206, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_65, c_203])).
% 2.08/1.37  tff(c_207, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_31, c_206])).
% 2.08/1.37  tff(c_180, plain, (![A_51, B_52]: (k1_relat_1(k2_zfmisc_1(A_51, B_52))=A_51 | k1_xboole_0=B_52 | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.37  tff(c_6, plain, (![A_4]: (v1_xboole_0(k1_relat_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.37  tff(c_189, plain, (![A_51, B_52]: (v1_xboole_0(A_51) | ~v1_xboole_0(k2_zfmisc_1(A_51, B_52)) | k1_xboole_0=B_52 | k1_xboole_0=A_51)), inference(superposition, [status(thm), theory('equality')], [c_180, c_6])).
% 2.08/1.37  tff(c_213, plain, (v1_xboole_0('#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_207, c_189])).
% 2.08/1.37  tff(c_225, plain, (v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_213])).
% 2.08/1.37  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.37  tff(c_233, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_225, c_2])).
% 2.08/1.37  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_233])).
% 2.08/1.37  tff(c_239, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.08/1.37  tff(c_370, plain, (![A_82, B_83]: (k4_tarski(k1_mcart_1(A_82), k2_mcart_1(A_82))=A_82 | ~r2_hidden(A_82, B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.37  tff(c_375, plain, (![A_86, B_87]: (k4_tarski(k1_mcart_1(A_86), k2_mcart_1(A_86))=A_86 | ~v1_relat_1(B_87) | v1_xboole_0(B_87) | ~m1_subset_1(A_86, B_87))), inference(resolution, [status(thm)], [c_4, c_370])).
% 2.08/1.37  tff(c_377, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_375])).
% 2.08/1.37  tff(c_380, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_239, c_377])).
% 2.08/1.37  tff(c_381, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_380])).
% 2.08/1.37  tff(c_341, plain, (![A_76, B_77]: (k1_relat_1(k2_zfmisc_1(A_76, B_77))=A_76 | k1_xboole_0=B_77 | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.37  tff(c_350, plain, (![A_76, B_77]: (v1_xboole_0(A_76) | ~v1_xboole_0(k2_zfmisc_1(A_76, B_77)) | k1_xboole_0=B_77 | k1_xboole_0=A_76)), inference(superposition, [status(thm), theory('equality')], [c_341, c_6])).
% 2.08/1.37  tff(c_387, plain, (v1_xboole_0('#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_381, c_350])).
% 2.08/1.37  tff(c_399, plain, (v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_387])).
% 2.08/1.37  tff(c_407, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_399, c_2])).
% 2.08/1.37  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_407])).
% 2.08/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.37  
% 2.08/1.37  Inference rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Ref     : 0
% 2.08/1.37  #Sup     : 76
% 2.08/1.37  #Fact    : 0
% 2.08/1.37  #Define  : 0
% 2.08/1.37  #Split   : 3
% 2.08/1.37  #Chain   : 0
% 2.08/1.37  #Close   : 0
% 2.08/1.37  
% 2.08/1.37  Ordering : KBO
% 2.08/1.37  
% 2.08/1.37  Simplification rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Subsume      : 16
% 2.08/1.37  #Demod        : 22
% 2.08/1.37  #Tautology    : 42
% 2.08/1.37  #SimpNegUnit  : 14
% 2.08/1.37  #BackRed      : 1
% 2.08/1.37  
% 2.08/1.37  #Partial instantiations: 0
% 2.08/1.37  #Strategies tried      : 1
% 2.08/1.37  
% 2.08/1.37  Timing (in seconds)
% 2.08/1.37  ----------------------
% 2.08/1.38  Preprocessing        : 0.29
% 2.08/1.38  Parsing              : 0.16
% 2.08/1.38  CNF conversion       : 0.02
% 2.08/1.38  Main loop            : 0.22
% 2.08/1.38  Inferencing          : 0.09
% 2.08/1.38  Reduction            : 0.06
% 2.08/1.38  Demodulation         : 0.04
% 2.08/1.38  BG Simplification    : 0.01
% 2.08/1.38  Subsumption          : 0.04
% 2.08/1.38  Abstraction          : 0.01
% 2.08/1.38  MUC search           : 0.00
% 2.08/1.38  Cooper               : 0.00
% 2.08/1.38  Total                : 0.54
% 2.08/1.38  Index Insertion      : 0.00
% 2.08/1.38  Index Deletion       : 0.00
% 2.08/1.38  Index Matching       : 0.00
% 2.08/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
