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
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  94 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_38,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [A_24] : k1_tarski(A_24) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_170,plain,(
    ! [D_71,C_72,B_73,A_74] :
      ( r2_hidden(k1_funct_1(D_71,C_72),B_73)
      | k1_xboole_0 = B_73
      | ~ r2_hidden(C_72,A_74)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(D_71,A_74,B_73)
      | ~ v1_funct_1(D_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,(
    ! [D_75,B_76] :
      ( r2_hidden(k1_funct_1(D_75,'#skF_5'),B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_76)))
      | ~ v1_funct_2(D_75,'#skF_3',B_76)
      | ~ v1_funct_1(D_75) ) ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_198,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_195])).

tff(c_201,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_198])).

tff(c_202,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_201])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [E_46,C_47,B_48,A_49] :
      ( E_46 = C_47
      | E_46 = B_48
      | E_46 = A_49
      | ~ r2_hidden(E_46,k1_enumset1(A_49,B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [E_54,B_55,A_56] :
      ( E_54 = B_55
      | E_54 = A_56
      | E_54 = A_56
      | ~ r2_hidden(E_54,k2_tarski(A_56,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_112])).

tff(c_141,plain,(
    ! [E_54,A_10] :
      ( E_54 = A_10
      | E_54 = A_10
      | E_54 = A_10
      | ~ r2_hidden(E_54,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_132])).

tff(c_207,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_202,c_141])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_38,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.35  
% 2.18/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.18/1.35  
% 2.18/1.35  %Foreground sorts:
% 2.18/1.35  
% 2.18/1.35  
% 2.18/1.35  %Background operators:
% 2.18/1.35  
% 2.18/1.35  
% 2.18/1.35  %Foreground operators:
% 2.18/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.18/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.35  
% 2.21/1.37  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.21/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.21/1.37  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.21/1.37  tff(f_63, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.21/1.37  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.37  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.37  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.21/1.37  tff(c_38, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.37  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.37  tff(c_65, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.37  tff(c_69, plain, (![A_24]: (k1_tarski(A_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 2.21/1.37  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.37  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.37  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.37  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.37  tff(c_170, plain, (![D_71, C_72, B_73, A_74]: (r2_hidden(k1_funct_1(D_71, C_72), B_73) | k1_xboole_0=B_73 | ~r2_hidden(C_72, A_74) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(D_71, A_74, B_73) | ~v1_funct_1(D_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.37  tff(c_195, plain, (![D_75, B_76]: (r2_hidden(k1_funct_1(D_75, '#skF_5'), B_76) | k1_xboole_0=B_76 | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_76))) | ~v1_funct_2(D_75, '#skF_3', B_76) | ~v1_funct_1(D_75))), inference(resolution, [status(thm)], [c_40, c_170])).
% 2.21/1.37  tff(c_198, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_195])).
% 2.21/1.37  tff(c_201, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_198])).
% 2.21/1.37  tff(c_202, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_69, c_201])).
% 2.21/1.37  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.37  tff(c_30, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.37  tff(c_112, plain, (![E_46, C_47, B_48, A_49]: (E_46=C_47 | E_46=B_48 | E_46=A_49 | ~r2_hidden(E_46, k1_enumset1(A_49, B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.37  tff(c_132, plain, (![E_54, B_55, A_56]: (E_54=B_55 | E_54=A_56 | E_54=A_56 | ~r2_hidden(E_54, k2_tarski(A_56, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_112])).
% 2.21/1.37  tff(c_141, plain, (![E_54, A_10]: (E_54=A_10 | E_54=A_10 | E_54=A_10 | ~r2_hidden(E_54, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_132])).
% 2.21/1.37  tff(c_207, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_202, c_141])).
% 2.21/1.37  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_38, c_207])).
% 2.21/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.37  
% 2.21/1.37  Inference rules
% 2.21/1.37  ----------------------
% 2.21/1.37  #Ref     : 0
% 2.21/1.37  #Sup     : 36
% 2.21/1.37  #Fact    : 0
% 2.21/1.37  #Define  : 0
% 2.21/1.37  #Split   : 0
% 2.21/1.37  #Chain   : 0
% 2.21/1.37  #Close   : 0
% 2.21/1.37  
% 2.21/1.37  Ordering : KBO
% 2.21/1.37  
% 2.21/1.37  Simplification rules
% 2.21/1.37  ----------------------
% 2.21/1.37  #Subsume      : 0
% 2.21/1.37  #Demod        : 4
% 2.21/1.37  #Tautology    : 16
% 2.21/1.37  #SimpNegUnit  : 2
% 2.21/1.37  #BackRed      : 0
% 2.21/1.37  
% 2.21/1.37  #Partial instantiations: 0
% 2.21/1.37  #Strategies tried      : 1
% 2.21/1.37  
% 2.21/1.37  Timing (in seconds)
% 2.21/1.37  ----------------------
% 2.21/1.37  Preprocessing        : 0.31
% 2.21/1.37  Parsing              : 0.16
% 2.21/1.37  CNF conversion       : 0.02
% 2.21/1.37  Main loop            : 0.18
% 2.21/1.37  Inferencing          : 0.06
% 2.21/1.37  Reduction            : 0.06
% 2.21/1.37  Demodulation         : 0.04
% 2.21/1.37  BG Simplification    : 0.01
% 2.21/1.37  Subsumption          : 0.04
% 2.21/1.37  Abstraction          : 0.02
% 2.21/1.37  MUC search           : 0.00
% 2.21/1.37  Cooper               : 0.00
% 2.21/1.37  Total                : 0.52
% 2.21/1.37  Index Insertion      : 0.00
% 2.21/1.37  Index Deletion       : 0.00
% 2.21/1.37  Index Matching       : 0.00
% 2.21/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
