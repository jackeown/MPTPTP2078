%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   53 (  57 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  70 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [A_55,B_56] : k4_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_8] : k4_xboole_0(k1_tarski(A_8),k1_tarski(A_8)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_32,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_32])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_286,plain,(
    ! [D_109,C_110,B_111,A_112] :
      ( r2_hidden(k1_funct_1(D_109,C_110),B_111)
      | k1_xboole_0 = B_111
      | ~ r2_hidden(C_110,A_112)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(D_109,A_112,B_111)
      | ~ v1_funct_1(D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_299,plain,(
    ! [D_113,B_114] :
      ( r2_hidden(k1_funct_1(D_113,'#skF_5'),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_114)))
      | ~ v1_funct_2(D_113,'#skF_3',B_114)
      | ~ v1_funct_1(D_113) ) ),
    inference(resolution,[status(thm)],[c_46,c_286])).

tff(c_302,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_299])).

tff(c_305,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_302])).

tff(c_306,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_305])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_312,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.39  
% 2.36/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.36/1.40  
% 2.36/1.40  %Foreground sorts:
% 2.36/1.40  
% 2.36/1.40  
% 2.36/1.40  %Background operators:
% 2.36/1.40  
% 2.36/1.40  
% 2.36/1.40  %Foreground operators:
% 2.36/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.40  
% 2.36/1.41  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.36/1.41  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.41  tff(f_57, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.36/1.41  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.36/1.41  tff(f_73, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.36/1.41  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.41  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.41  tff(c_16, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.41  tff(c_79, plain, (![A_55, B_56]: (k4_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.36/1.41  tff(c_86, plain, (![A_8]: (k4_xboole_0(k1_tarski(A_8), k1_tarski(A_8))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 2.36/1.41  tff(c_32, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.41  tff(c_89, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_32])).
% 2.36/1.41  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.41  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.41  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.41  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.41  tff(c_286, plain, (![D_109, C_110, B_111, A_112]: (r2_hidden(k1_funct_1(D_109, C_110), B_111) | k1_xboole_0=B_111 | ~r2_hidden(C_110, A_112) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(D_109, A_112, B_111) | ~v1_funct_1(D_109))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.41  tff(c_299, plain, (![D_113, B_114]: (r2_hidden(k1_funct_1(D_113, '#skF_5'), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_114))) | ~v1_funct_2(D_113, '#skF_3', B_114) | ~v1_funct_1(D_113))), inference(resolution, [status(thm)], [c_46, c_286])).
% 2.36/1.41  tff(c_302, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_299])).
% 2.36/1.41  tff(c_305, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_302])).
% 2.36/1.41  tff(c_306, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_89, c_305])).
% 2.36/1.41  tff(c_4, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.41  tff(c_312, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_306, c_4])).
% 2.36/1.41  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_312])).
% 2.36/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.41  
% 2.36/1.41  Inference rules
% 2.36/1.41  ----------------------
% 2.36/1.41  #Ref     : 0
% 2.36/1.41  #Sup     : 58
% 2.36/1.41  #Fact    : 0
% 2.36/1.41  #Define  : 0
% 2.36/1.41  #Split   : 0
% 2.36/1.41  #Chain   : 0
% 2.36/1.41  #Close   : 0
% 2.36/1.41  
% 2.36/1.41  Ordering : KBO
% 2.36/1.41  
% 2.36/1.41  Simplification rules
% 2.36/1.41  ----------------------
% 2.36/1.41  #Subsume      : 0
% 2.36/1.41  #Demod        : 10
% 2.36/1.41  #Tautology    : 45
% 2.36/1.41  #SimpNegUnit  : 4
% 2.36/1.41  #BackRed      : 1
% 2.36/1.41  
% 2.36/1.41  #Partial instantiations: 0
% 2.36/1.41  #Strategies tried      : 1
% 2.36/1.41  
% 2.36/1.41  Timing (in seconds)
% 2.36/1.41  ----------------------
% 2.36/1.41  Preprocessing        : 0.35
% 2.36/1.41  Parsing              : 0.19
% 2.36/1.41  CNF conversion       : 0.02
% 2.36/1.41  Main loop            : 0.21
% 2.36/1.41  Inferencing          : 0.08
% 2.36/1.41  Reduction            : 0.06
% 2.36/1.41  Demodulation         : 0.05
% 2.36/1.41  BG Simplification    : 0.02
% 2.36/1.41  Subsumption          : 0.03
% 2.36/1.41  Abstraction          : 0.02
% 2.36/1.41  MUC search           : 0.00
% 2.36/1.41  Cooper               : 0.00
% 2.36/1.41  Total                : 0.58
% 2.36/1.41  Index Insertion      : 0.00
% 2.36/1.41  Index Deletion       : 0.00
% 2.36/1.41  Index Matching       : 0.00
% 2.36/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
