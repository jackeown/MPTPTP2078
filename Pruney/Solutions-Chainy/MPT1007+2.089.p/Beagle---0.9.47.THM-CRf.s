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
% DateTime   : Thu Dec  3 10:14:23 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 119 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_252,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_252])).

tff(c_267,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_259])).

tff(c_268,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_267])).

tff(c_101,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1(k1_relset_1(A_41,B_42,C_43),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k1_relset_1(A_44,B_45,C_46),A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(resolution,[status(thm)],[c_101,c_12])).

tff(c_116,plain,(
    r1_tarski(k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_270,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_116])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_26,C_27,B_28] :
      ( r2_hidden(A_26,C_27)
      | ~ r1_tarski(k2_tarski(A_26,B_28),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_1,C_27] :
      ( r2_hidden(A_1,C_27)
      | ~ r1_tarski(k1_tarski(A_1),C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_288,plain,(
    r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_270,c_72])).

tff(c_30,plain,(
    ! [D_18,C_17,B_16,A_15] :
      ( r2_hidden(k1_funct_1(D_18,C_17),B_16)
      | k1_xboole_0 = B_16
      | ~ r2_hidden(C_17,A_15)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(D_18,A_15,B_16)
      | ~ v1_funct_1(D_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_299,plain,(
    ! [D_81,B_82] :
      ( r2_hidden(k1_funct_1(D_81,'#skF_1'),B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),B_82)))
      | ~ v1_funct_2(D_81,k1_tarski('#skF_1'),B_82)
      | ~ v1_funct_1(D_81) ) ),
    inference(resolution,[status(thm)],[c_288,c_30])).

tff(c_306,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_299])).

tff(c_314,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_306])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:52:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.30  
% 2.27/1.30  %Foreground sorts:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Background operators:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Foreground operators:
% 2.27/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.30  
% 2.27/1.32  tff(f_85, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.27/1.32  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.32  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.27/1.32  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.27/1.32  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.32  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.27/1.32  tff(f_73, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.27/1.32  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.32  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.32  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.32  tff(c_38, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.32  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.32  tff(c_252, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.32  tff(c_259, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_252])).
% 2.27/1.32  tff(c_267, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_259])).
% 2.27/1.32  tff(c_268, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_267])).
% 2.27/1.32  tff(c_101, plain, (![A_41, B_42, C_43]: (m1_subset_1(k1_relset_1(A_41, B_42, C_43), k1_zfmisc_1(A_41)) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.32  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.32  tff(c_106, plain, (![A_44, B_45, C_46]: (r1_tarski(k1_relset_1(A_44, B_45, C_46), A_44) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(resolution, [status(thm)], [c_101, c_12])).
% 2.27/1.32  tff(c_116, plain, (r1_tarski(k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.27/1.32  tff(c_270, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_116])).
% 2.27/1.32  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.32  tff(c_69, plain, (![A_26, C_27, B_28]: (r2_hidden(A_26, C_27) | ~r1_tarski(k2_tarski(A_26, B_28), C_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.32  tff(c_72, plain, (![A_1, C_27]: (r2_hidden(A_1, C_27) | ~r1_tarski(k1_tarski(A_1), C_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 2.27/1.32  tff(c_288, plain, (r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_270, c_72])).
% 2.27/1.32  tff(c_30, plain, (![D_18, C_17, B_16, A_15]: (r2_hidden(k1_funct_1(D_18, C_17), B_16) | k1_xboole_0=B_16 | ~r2_hidden(C_17, A_15) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(D_18, A_15, B_16) | ~v1_funct_1(D_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.32  tff(c_299, plain, (![D_81, B_82]: (r2_hidden(k1_funct_1(D_81, '#skF_1'), B_82) | k1_xboole_0=B_82 | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), B_82))) | ~v1_funct_2(D_81, k1_tarski('#skF_1'), B_82) | ~v1_funct_1(D_81))), inference(resolution, [status(thm)], [c_288, c_30])).
% 2.27/1.32  tff(c_306, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_299])).
% 2.27/1.32  tff(c_314, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_306])).
% 2.27/1.32  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_314])).
% 2.27/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  Inference rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Ref     : 0
% 2.27/1.32  #Sup     : 54
% 2.27/1.32  #Fact    : 0
% 2.27/1.32  #Define  : 0
% 2.27/1.32  #Split   : 0
% 2.27/1.32  #Chain   : 0
% 2.27/1.32  #Close   : 0
% 2.27/1.32  
% 2.27/1.32  Ordering : KBO
% 2.27/1.32  
% 2.27/1.32  Simplification rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Subsume      : 1
% 2.27/1.32  #Demod        : 10
% 2.27/1.32  #Tautology    : 16
% 2.27/1.32  #SimpNegUnit  : 4
% 2.27/1.32  #BackRed      : 1
% 2.27/1.32  
% 2.27/1.32  #Partial instantiations: 0
% 2.27/1.32  #Strategies tried      : 1
% 2.27/1.32  
% 2.27/1.32  Timing (in seconds)
% 2.27/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.32
% 2.27/1.32  Parsing              : 0.17
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.23
% 2.27/1.32  Inferencing          : 0.09
% 2.27/1.32  Reduction            : 0.07
% 2.27/1.32  Demodulation         : 0.05
% 2.27/1.32  BG Simplification    : 0.02
% 2.27/1.32  Subsumption          : 0.04
% 2.27/1.32  Abstraction          : 0.01
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.32  Total                : 0.59
% 2.27/1.32  Index Insertion      : 0.00
% 2.27/1.32  Index Deletion       : 0.00
% 2.27/1.32  Index Matching       : 0.00
% 2.27/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
