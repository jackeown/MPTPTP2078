%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  82 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [A_35,B_36] : k2_xboole_0(k1_tarski(A_35),k1_tarski(B_36)) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),B_20) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    ! [A_37,B_38] : k2_tarski(A_37,B_38) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_30])).

tff(c_85,plain,(
    ! [A_9] : k1_tarski(A_9) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2051,plain,(
    ! [D_3404,C_3405,B_3406,A_3407] :
      ( r2_hidden(k1_funct_1(D_3404,C_3405),B_3406)
      | k1_xboole_0 = B_3406
      | ~ r2_hidden(C_3405,A_3407)
      | ~ m1_subset_1(D_3404,k1_zfmisc_1(k2_zfmisc_1(A_3407,B_3406)))
      | ~ v1_funct_2(D_3404,A_3407,B_3406)
      | ~ v1_funct_1(D_3404) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2978,plain,(
    ! [D_4260,B_4261] :
      ( r2_hidden(k1_funct_1(D_4260,'#skF_5'),B_4261)
      | k1_xboole_0 = B_4261
      | ~ m1_subset_1(D_4260,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_4261)))
      | ~ v1_funct_2(D_4260,'#skF_3',B_4261)
      | ~ v1_funct_1(D_4260) ) ),
    inference(resolution,[status(thm)],[c_36,c_2051])).

tff(c_2987,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_2978])).

tff(c_2990,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2987])).

tff(c_2991,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2990])).

tff(c_96,plain,(
    ! [D_43,B_44,A_45] :
      ( D_43 = B_44
      | D_43 = A_45
      | ~ r2_hidden(D_43,k2_tarski(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [D_43,A_9] :
      ( D_43 = A_9
      | D_43 = A_9
      | ~ r2_hidden(D_43,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_96])).

tff(c_2996,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2991,c_99])).

tff(c_3042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_2996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.65  
% 3.50/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.66  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.50/1.66  
% 3.50/1.66  %Foreground sorts:
% 3.50/1.66  
% 3.50/1.66  
% 3.50/1.66  %Background operators:
% 3.50/1.66  
% 3.50/1.66  
% 3.50/1.66  %Foreground operators:
% 3.50/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.50/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.50/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.50/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.50/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.50/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.50/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.66  
% 3.82/1.67  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.82/1.67  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/1.67  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.82/1.67  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.82/1.67  tff(f_59, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.82/1.67  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.82/1.67  tff(c_34, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.67  tff(c_22, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.67  tff(c_72, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(B_36))=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.82/1.67  tff(c_30, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.67  tff(c_83, plain, (![A_37, B_38]: (k2_tarski(A_37, B_38)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_30])).
% 3.82/1.67  tff(c_85, plain, (![A_9]: (k1_tarski(A_9)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_83])).
% 3.82/1.67  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.67  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.67  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.67  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.67  tff(c_2051, plain, (![D_3404, C_3405, B_3406, A_3407]: (r2_hidden(k1_funct_1(D_3404, C_3405), B_3406) | k1_xboole_0=B_3406 | ~r2_hidden(C_3405, A_3407) | ~m1_subset_1(D_3404, k1_zfmisc_1(k2_zfmisc_1(A_3407, B_3406))) | ~v1_funct_2(D_3404, A_3407, B_3406) | ~v1_funct_1(D_3404))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.82/1.67  tff(c_2978, plain, (![D_4260, B_4261]: (r2_hidden(k1_funct_1(D_4260, '#skF_5'), B_4261) | k1_xboole_0=B_4261 | ~m1_subset_1(D_4260, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_4261))) | ~v1_funct_2(D_4260, '#skF_3', B_4261) | ~v1_funct_1(D_4260))), inference(resolution, [status(thm)], [c_36, c_2051])).
% 3.82/1.67  tff(c_2987, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_2978])).
% 3.82/1.67  tff(c_2990, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2987])).
% 3.82/1.67  tff(c_2991, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_85, c_2990])).
% 3.82/1.67  tff(c_96, plain, (![D_43, B_44, A_45]: (D_43=B_44 | D_43=A_45 | ~r2_hidden(D_43, k2_tarski(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.67  tff(c_99, plain, (![D_43, A_9]: (D_43=A_9 | D_43=A_9 | ~r2_hidden(D_43, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_96])).
% 3.82/1.67  tff(c_2996, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2991, c_99])).
% 3.82/1.67  tff(c_3042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_2996])).
% 3.82/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.67  
% 3.82/1.67  Inference rules
% 3.82/1.67  ----------------------
% 3.82/1.67  #Ref     : 0
% 3.82/1.67  #Sup     : 393
% 3.82/1.67  #Fact    : 8
% 3.82/1.67  #Define  : 0
% 3.82/1.67  #Split   : 7
% 3.82/1.67  #Chain   : 0
% 3.82/1.67  #Close   : 0
% 3.82/1.67  
% 3.82/1.67  Ordering : KBO
% 3.82/1.67  
% 3.82/1.67  Simplification rules
% 3.82/1.67  ----------------------
% 3.82/1.67  #Subsume      : 77
% 3.82/1.67  #Demod        : 51
% 3.82/1.67  #Tautology    : 132
% 3.82/1.67  #SimpNegUnit  : 19
% 3.82/1.67  #BackRed      : 0
% 3.82/1.67  
% 3.82/1.67  #Partial instantiations: 2496
% 3.82/1.67  #Strategies tried      : 1
% 3.82/1.67  
% 3.82/1.67  Timing (in seconds)
% 3.82/1.67  ----------------------
% 3.82/1.67  Preprocessing        : 0.30
% 3.82/1.67  Parsing              : 0.16
% 3.82/1.67  CNF conversion       : 0.02
% 3.82/1.67  Main loop            : 0.61
% 3.82/1.67  Inferencing          : 0.33
% 3.82/1.67  Reduction            : 0.13
% 3.82/1.67  Demodulation         : 0.09
% 3.82/1.67  BG Simplification    : 0.03
% 3.82/1.67  Subsumption          : 0.08
% 3.82/1.67  Abstraction          : 0.04
% 3.82/1.67  MUC search           : 0.00
% 3.82/1.67  Cooper               : 0.00
% 3.82/1.67  Total                : 0.94
% 3.82/1.67  Index Insertion      : 0.00
% 3.82/1.67  Index Deletion       : 0.00
% 3.82/1.67  Index Matching       : 0.00
% 3.82/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
