%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   59 (  67 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  92 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_18] : k1_setfam_1(k1_tarski(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = k1_setfam_1(k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_84])).

tff(c_96,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_116,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_116])).

tff(c_128,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_30,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [B_17] : k1_tarski(B_17) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_30])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3452,plain,(
    ! [D_10829,C_10830,B_10831,A_10832] :
      ( r2_hidden(k1_funct_1(D_10829,C_10830),B_10831)
      | k1_xboole_0 = B_10831
      | ~ r2_hidden(C_10830,A_10832)
      | ~ m1_subset_1(D_10829,k1_zfmisc_1(k2_zfmisc_1(A_10832,B_10831)))
      | ~ v1_funct_2(D_10829,A_10832,B_10831)
      | ~ v1_funct_1(D_10829) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3653,plain,(
    ! [D_11424,B_11425] :
      ( r2_hidden(k1_funct_1(D_11424,'#skF_5'),B_11425)
      | k1_xboole_0 = B_11425
      | ~ m1_subset_1(D_11424,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_11425)))
      | ~ v1_funct_2(D_11424,'#skF_3',B_11425)
      | ~ v1_funct_1(D_11424) ) ),
    inference(resolution,[status(thm)],[c_42,c_3452])).

tff(c_3670,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_3653])).

tff(c_3673,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3670])).

tff(c_3674,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_3673])).

tff(c_160,plain,(
    ! [D_45,B_46,A_47] :
      ( D_45 = B_46
      | D_45 = A_47
      | ~ r2_hidden(D_45,k2_tarski(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [D_45,A_10] :
      ( D_45 = A_10
      | D_45 = A_10
      | ~ r2_hidden(D_45,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_160])).

tff(c_3679,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3674,c_169])).

tff(c_3736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_3679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:19:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.97  
% 3.82/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.97  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.82/1.97  
% 3.82/1.97  %Foreground sorts:
% 3.82/1.97  
% 3.82/1.97  
% 3.82/1.97  %Background operators:
% 3.82/1.97  
% 3.82/1.97  
% 3.82/1.97  %Foreground operators:
% 3.82/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.82/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.82/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.82/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/1.97  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.82/1.97  tff('#skF_6', type, '#skF_6': $i).
% 3.82/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.82/1.97  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.82/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.97  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.82/1.97  
% 3.82/1.98  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.82/1.98  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.82/1.98  tff(f_51, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.82/1.98  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/1.98  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.82/1.98  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.82/1.98  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.82/1.98  tff(f_65, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.82/1.98  tff(f_38, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.82/1.98  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.98  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.82/1.98  tff(c_34, plain, (![A_18]: (k1_setfam_1(k1_tarski(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.98  tff(c_24, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.82/1.98  tff(c_84, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.82/1.98  tff(c_93, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=k1_setfam_1(k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_84])).
% 3.82/1.98  tff(c_96, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_93])).
% 3.82/1.98  tff(c_116, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.98  tff(c_125, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_96, c_116])).
% 3.82/1.98  tff(c_128, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 3.82/1.98  tff(c_30, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.82/1.98  tff(c_129, plain, (![B_17]: (k1_tarski(B_17)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_30])).
% 3.82/1.98  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.98  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.98  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.98  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.98  tff(c_3452, plain, (![D_10829, C_10830, B_10831, A_10832]: (r2_hidden(k1_funct_1(D_10829, C_10830), B_10831) | k1_xboole_0=B_10831 | ~r2_hidden(C_10830, A_10832) | ~m1_subset_1(D_10829, k1_zfmisc_1(k2_zfmisc_1(A_10832, B_10831))) | ~v1_funct_2(D_10829, A_10832, B_10831) | ~v1_funct_1(D_10829))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.82/1.98  tff(c_3653, plain, (![D_11424, B_11425]: (r2_hidden(k1_funct_1(D_11424, '#skF_5'), B_11425) | k1_xboole_0=B_11425 | ~m1_subset_1(D_11424, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_11425))) | ~v1_funct_2(D_11424, '#skF_3', B_11425) | ~v1_funct_1(D_11424))), inference(resolution, [status(thm)], [c_42, c_3452])).
% 3.82/1.98  tff(c_3670, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_3653])).
% 3.82/1.98  tff(c_3673, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3670])).
% 3.82/1.98  tff(c_3674, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_129, c_3673])).
% 3.82/1.98  tff(c_160, plain, (![D_45, B_46, A_47]: (D_45=B_46 | D_45=A_47 | ~r2_hidden(D_45, k2_tarski(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.98  tff(c_169, plain, (![D_45, A_10]: (D_45=A_10 | D_45=A_10 | ~r2_hidden(D_45, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_160])).
% 3.82/1.98  tff(c_3679, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3674, c_169])).
% 3.82/1.98  tff(c_3736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_3679])).
% 3.82/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.98  
% 3.82/1.98  Inference rules
% 3.82/1.98  ----------------------
% 3.82/1.98  #Ref     : 0
% 3.82/1.98  #Sup     : 417
% 3.82/1.98  #Fact    : 8
% 3.82/1.98  #Define  : 0
% 3.82/1.98  #Split   : 5
% 3.82/1.98  #Chain   : 0
% 3.82/1.98  #Close   : 0
% 3.82/1.98  
% 3.82/1.98  Ordering : KBO
% 3.82/1.98  
% 3.82/1.98  Simplification rules
% 3.82/1.98  ----------------------
% 3.82/1.98  #Subsume      : 63
% 3.82/1.98  #Demod        : 57
% 3.82/1.98  #Tautology    : 144
% 3.82/1.98  #SimpNegUnit  : 23
% 3.82/1.98  #BackRed      : 1
% 3.82/1.98  
% 3.82/1.98  #Partial instantiations: 4926
% 3.82/1.98  #Strategies tried      : 1
% 3.82/1.98  
% 3.82/1.98  Timing (in seconds)
% 3.82/1.98  ----------------------
% 3.82/1.98  Preprocessing        : 0.44
% 3.82/1.98  Parsing              : 0.25
% 3.82/1.98  CNF conversion       : 0.03
% 4.16/1.98  Main loop            : 0.65
% 4.16/1.98  Inferencing          : 0.37
% 4.16/1.98  Reduction            : 0.13
% 4.16/1.98  Demodulation         : 0.09
% 4.16/1.98  BG Simplification    : 0.03
% 4.16/1.98  Subsumption          : 0.07
% 4.16/1.98  Abstraction          : 0.03
% 4.16/1.98  MUC search           : 0.00
% 4.16/1.98  Cooper               : 0.00
% 4.16/1.98  Total                : 1.12
% 4.16/1.98  Index Insertion      : 0.00
% 4.16/1.98  Index Deletion       : 0.00
% 4.16/1.98  Index Matching       : 0.00
% 4.16/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
