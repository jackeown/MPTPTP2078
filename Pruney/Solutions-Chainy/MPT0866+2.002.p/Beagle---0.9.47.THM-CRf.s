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
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 13.84s
% Output     : CNFRefutation 13.90s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 130 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [D_42,B_43] : r2_hidden(D_42,k2_tarski(D_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_28,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(k1_tarski(B_11),k1_zfmisc_1(A_10))
      | k1_xboole_0 = A_10
      | ~ m1_subset_1(B_11,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6962,plain,(
    ! [A_7778,B_7779,C_7780,D_7781] :
      ( k4_tarski('#skF_6'(A_7778,B_7779,C_7780,D_7781),'#skF_7'(A_7778,B_7779,C_7780,D_7781)) = A_7778
      | ~ r2_hidden(A_7778,D_7781)
      | ~ m1_subset_1(D_7781,k1_zfmisc_1(k2_zfmisc_1(B_7779,C_7780))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45321,plain,(
    ! [A_27017,B_27018,C_27019,B_27020] :
      ( k4_tarski('#skF_6'(A_27017,B_27018,C_27019,k1_tarski(B_27020)),'#skF_7'(A_27017,B_27018,C_27019,k1_tarski(B_27020))) = A_27017
      | ~ r2_hidden(A_27017,k1_tarski(B_27020))
      | k2_zfmisc_1(B_27018,C_27019) = k1_xboole_0
      | ~ m1_subset_1(B_27020,k2_zfmisc_1(B_27018,C_27019)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6962])).

tff(c_137,plain,(
    ! [A_61,B_62] :
      ( k4_tarski(k1_mcart_1(A_61),k2_mcart_1(A_61)) = A_61
      | ~ r2_hidden(A_61,B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    ! [A_63] :
      ( k4_tarski(k1_mcart_1(A_63),k2_mcart_1(A_63)) = A_63
      | ~ v1_relat_1(k1_tarski(A_63)) ) ),
    inference(resolution,[status(thm)],[c_85,c_137])).

tff(c_44,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_162,plain,(
    ~ v1_relat_1(k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_44])).

tff(c_34,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_105,plain,(
    ! [D_53,B_54,A_55] :
      ( D_53 = B_54
      | D_53 = A_55
      | ~ r2_hidden(D_53,k2_tarski(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [D_56,A_57] :
      ( D_56 = A_57
      | D_56 = A_57
      | ~ r2_hidden(D_56,k1_tarski(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_132,plain,(
    ! [A_57] :
      ( '#skF_3'(k1_tarski(A_57)) = A_57
      | v1_relat_1(k1_tarski(A_57)) ) ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_167,plain,(
    '#skF_3'(k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_132,c_162])).

tff(c_32,plain,(
    ! [C_25,D_26,A_12] :
      ( k4_tarski(C_25,D_26) != '#skF_3'(A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    ! [C_25,D_26] :
      ( k4_tarski(C_25,D_26) != '#skF_10'
      | v1_relat_1(k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_32])).

tff(c_176,plain,(
    ! [C_25,D_26] : k4_tarski(C_25,D_26) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_170])).

tff(c_45683,plain,(
    ! [A_27285,B_27286,B_27287,C_27288] :
      ( A_27285 != '#skF_10'
      | ~ r2_hidden(A_27285,k1_tarski(B_27286))
      | k2_zfmisc_1(B_27287,C_27288) = k1_xboole_0
      | ~ m1_subset_1(B_27286,k2_zfmisc_1(B_27287,C_27288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45321,c_176])).

tff(c_45732,plain,(
    ! [A_27376,B_27377,C_27378] :
      ( A_27376 != '#skF_10'
      | k2_zfmisc_1(B_27377,C_27378) = k1_xboole_0
      | ~ m1_subset_1(A_27376,k2_zfmisc_1(B_27377,C_27378)) ) ),
    inference(resolution,[status(thm)],[c_85,c_45683])).

tff(c_45745,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_45732])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45761,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_45745,c_22])).

tff(c_45771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_45761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.84/5.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.84/5.90  
% 13.84/5.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.84/5.90  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 13.84/5.90  
% 13.84/5.90  %Foreground sorts:
% 13.84/5.90  
% 13.84/5.90  
% 13.84/5.90  %Background operators:
% 13.84/5.90  
% 13.84/5.90  
% 13.84/5.90  %Foreground operators:
% 13.84/5.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.84/5.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.84/5.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.84/5.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.84/5.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.84/5.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.84/5.90  tff('#skF_10', type, '#skF_10': $i).
% 13.84/5.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.84/5.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.84/5.90  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 13.84/5.90  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 13.84/5.90  tff('#skF_9', type, '#skF_9': $i).
% 13.84/5.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.84/5.90  tff('#skF_8', type, '#skF_8': $i).
% 13.84/5.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.84/5.90  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 13.84/5.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.84/5.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.84/5.90  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.84/5.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.84/5.90  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 13.84/5.90  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.84/5.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.84/5.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.84/5.90  
% 13.90/5.91  tff(f_92, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 13.90/5.91  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.90/5.91  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 13.90/5.91  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 13.90/5.91  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 13.90/5.91  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 13.90/5.91  tff(f_59, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 13.90/5.91  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.90/5.91  tff(c_50, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.90/5.91  tff(c_48, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.90/5.91  tff(c_46, plain, (m1_subset_1('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.90/5.91  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.90/5.91  tff(c_82, plain, (![D_42, B_43]: (r2_hidden(D_42, k2_tarski(D_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.90/5.91  tff(c_85, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 13.90/5.91  tff(c_28, plain, (![B_11, A_10]: (m1_subset_1(k1_tarski(B_11), k1_zfmisc_1(A_10)) | k1_xboole_0=A_10 | ~m1_subset_1(B_11, A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.90/5.91  tff(c_6962, plain, (![A_7778, B_7779, C_7780, D_7781]: (k4_tarski('#skF_6'(A_7778, B_7779, C_7780, D_7781), '#skF_7'(A_7778, B_7779, C_7780, D_7781))=A_7778 | ~r2_hidden(A_7778, D_7781) | ~m1_subset_1(D_7781, k1_zfmisc_1(k2_zfmisc_1(B_7779, C_7780))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.90/5.91  tff(c_45321, plain, (![A_27017, B_27018, C_27019, B_27020]: (k4_tarski('#skF_6'(A_27017, B_27018, C_27019, k1_tarski(B_27020)), '#skF_7'(A_27017, B_27018, C_27019, k1_tarski(B_27020)))=A_27017 | ~r2_hidden(A_27017, k1_tarski(B_27020)) | k2_zfmisc_1(B_27018, C_27019)=k1_xboole_0 | ~m1_subset_1(B_27020, k2_zfmisc_1(B_27018, C_27019)))), inference(resolution, [status(thm)], [c_28, c_6962])).
% 13.90/5.91  tff(c_137, plain, (![A_61, B_62]: (k4_tarski(k1_mcart_1(A_61), k2_mcart_1(A_61))=A_61 | ~r2_hidden(A_61, B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.90/5.91  tff(c_150, plain, (![A_63]: (k4_tarski(k1_mcart_1(A_63), k2_mcart_1(A_63))=A_63 | ~v1_relat_1(k1_tarski(A_63)))), inference(resolution, [status(thm)], [c_85, c_137])).
% 13.90/5.91  tff(c_44, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.90/5.91  tff(c_162, plain, (~v1_relat_1(k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_44])).
% 13.90/5.91  tff(c_34, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.90/5.91  tff(c_105, plain, (![D_53, B_54, A_55]: (D_53=B_54 | D_53=A_55 | ~r2_hidden(D_53, k2_tarski(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.90/5.91  tff(c_124, plain, (![D_56, A_57]: (D_56=A_57 | D_56=A_57 | ~r2_hidden(D_56, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_105])).
% 13.90/5.91  tff(c_132, plain, (![A_57]: ('#skF_3'(k1_tarski(A_57))=A_57 | v1_relat_1(k1_tarski(A_57)))), inference(resolution, [status(thm)], [c_34, c_124])).
% 13.90/5.91  tff(c_167, plain, ('#skF_3'(k1_tarski('#skF_10'))='#skF_10'), inference(resolution, [status(thm)], [c_132, c_162])).
% 13.90/5.91  tff(c_32, plain, (![C_25, D_26, A_12]: (k4_tarski(C_25, D_26)!='#skF_3'(A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.90/5.91  tff(c_170, plain, (![C_25, D_26]: (k4_tarski(C_25, D_26)!='#skF_10' | v1_relat_1(k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_32])).
% 13.90/5.91  tff(c_176, plain, (![C_25, D_26]: (k4_tarski(C_25, D_26)!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_162, c_170])).
% 13.90/5.91  tff(c_45683, plain, (![A_27285, B_27286, B_27287, C_27288]: (A_27285!='#skF_10' | ~r2_hidden(A_27285, k1_tarski(B_27286)) | k2_zfmisc_1(B_27287, C_27288)=k1_xboole_0 | ~m1_subset_1(B_27286, k2_zfmisc_1(B_27287, C_27288)))), inference(superposition, [status(thm), theory('equality')], [c_45321, c_176])).
% 13.90/5.91  tff(c_45732, plain, (![A_27376, B_27377, C_27378]: (A_27376!='#skF_10' | k2_zfmisc_1(B_27377, C_27378)=k1_xboole_0 | ~m1_subset_1(A_27376, k2_zfmisc_1(B_27377, C_27378)))), inference(resolution, [status(thm)], [c_85, c_45683])).
% 13.90/5.91  tff(c_45745, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_45732])).
% 13.90/5.91  tff(c_22, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.90/5.91  tff(c_45761, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_45745, c_22])).
% 13.90/5.91  tff(c_45771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_45761])).
% 13.90/5.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/5.91  
% 13.90/5.91  Inference rules
% 13.90/5.91  ----------------------
% 13.90/5.91  #Ref     : 33
% 13.90/5.91  #Sup     : 7803
% 13.90/5.91  #Fact    : 64
% 13.90/5.91  #Define  : 0
% 13.90/5.91  #Split   : 26
% 13.90/5.91  #Chain   : 0
% 13.90/5.91  #Close   : 0
% 13.90/5.91  
% 13.90/5.91  Ordering : KBO
% 13.90/5.91  
% 13.90/5.91  Simplification rules
% 13.90/5.91  ----------------------
% 13.90/5.91  #Subsume      : 4478
% 13.90/5.91  #Demod        : 1977
% 13.90/5.91  #Tautology    : 1346
% 13.90/5.91  #SimpNegUnit  : 647
% 13.90/5.91  #BackRed      : 111
% 13.90/5.91  
% 13.90/5.91  #Partial instantiations: 16704
% 13.90/5.91  #Strategies tried      : 1
% 13.90/5.91  
% 13.90/5.91  Timing (in seconds)
% 13.90/5.91  ----------------------
% 13.90/5.91  Preprocessing        : 0.37
% 13.90/5.91  Parsing              : 0.19
% 13.90/5.91  CNF conversion       : 0.03
% 13.90/5.91  Main loop            : 4.78
% 13.90/5.91  Inferencing          : 1.70
% 13.90/5.91  Reduction            : 1.26
% 13.90/5.91  Demodulation         : 0.83
% 13.90/5.91  BG Simplification    : 0.14
% 13.90/5.91  Subsumption          : 1.43
% 13.90/5.91  Abstraction          : 0.21
% 13.90/5.91  MUC search           : 0.00
% 13.90/5.91  Cooper               : 0.00
% 13.90/5.91  Total                : 5.18
% 13.90/5.91  Index Insertion      : 0.00
% 13.90/5.91  Index Deletion       : 0.00
% 13.90/5.91  Index Matching       : 0.00
% 13.90/5.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
