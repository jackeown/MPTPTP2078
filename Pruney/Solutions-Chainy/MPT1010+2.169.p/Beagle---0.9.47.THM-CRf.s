%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_64,axiom,(
    ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(f_62,axiom,(
    ! [A] : k3_relat_1(k1_tarski(k4_tarski(A,A))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_108,plain,(
    ! [A_42,B_43] : k3_relat_1(k1_tarski(k4_tarski(A_42,B_43))) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [A_19] : k3_relat_1(k1_tarski(k4_tarski(A_19,A_19))) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    ! [B_44] : k2_tarski(B_44,B_44) = k1_tarski(B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_36])).

tff(c_32,plain,(
    ! [B_17,C_18] : k4_xboole_0(k1_tarski(B_17),k2_tarski(B_17,C_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_32])).

tff(c_22,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_400,plain,(
    ! [D_87,C_88,B_89,A_90] :
      ( r2_hidden(k1_funct_1(D_87,C_88),B_89)
      | k1_xboole_0 = B_89
      | ~ r2_hidden(C_88,A_90)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(D_87,A_90,B_89)
      | ~ v1_funct_1(D_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_414,plain,(
    ! [D_91,B_92] :
      ( r2_hidden(k1_funct_1(D_91,'#skF_5'),B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_92)))
      | ~ v1_funct_2(D_91,'#skF_3',B_92)
      | ~ v1_funct_1(D_91) ) ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_417,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_414])).

tff(c_420,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_417])).

tff(c_421,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_420])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_426,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_421,c_2])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.59/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.59/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.40  
% 2.59/1.41  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.59/1.41  tff(f_64, axiom, (![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 2.59/1.41  tff(f_62, axiom, (![A]: (k3_relat_1(k1_tarski(k4_tarski(A, A))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t208_relat_1)).
% 2.59/1.41  tff(f_60, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.59/1.41  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.59/1.41  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.59/1.41  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.59/1.41  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.41  tff(c_108, plain, (![A_42, B_43]: (k3_relat_1(k1_tarski(k4_tarski(A_42, B_43)))=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_36, plain, (![A_19]: (k3_relat_1(k1_tarski(k4_tarski(A_19, A_19)))=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.41  tff(c_124, plain, (![B_44]: (k2_tarski(B_44, B_44)=k1_tarski(B_44))), inference(superposition, [status(thm), theory('equality')], [c_108, c_36])).
% 2.59/1.41  tff(c_32, plain, (![B_17, C_18]: (k4_xboole_0(k1_tarski(B_17), k2_tarski(B_17, C_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.41  tff(c_130, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_32])).
% 2.59/1.41  tff(c_22, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.41  tff(c_158, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 2.59/1.41  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.41  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.41  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.41  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.41  tff(c_400, plain, (![D_87, C_88, B_89, A_90]: (r2_hidden(k1_funct_1(D_87, C_88), B_89) | k1_xboole_0=B_89 | ~r2_hidden(C_88, A_90) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(D_87, A_90, B_89) | ~v1_funct_1(D_87))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.41  tff(c_414, plain, (![D_91, B_92]: (r2_hidden(k1_funct_1(D_91, '#skF_5'), B_92) | k1_xboole_0=B_92 | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_92))) | ~v1_funct_2(D_91, '#skF_3', B_92) | ~v1_funct_1(D_91))), inference(resolution, [status(thm)], [c_46, c_400])).
% 2.59/1.41  tff(c_417, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_414])).
% 2.59/1.41  tff(c_420, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_417])).
% 2.59/1.41  tff(c_421, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_158, c_420])).
% 2.59/1.41  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_426, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_421, c_2])).
% 2.59/1.41  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_426])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 82
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 0
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 1
% 2.59/1.41  #Demod        : 25
% 2.59/1.41  #Tautology    : 64
% 2.59/1.41  #SimpNegUnit  : 10
% 2.59/1.41  #BackRed      : 1
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.42  Preprocessing        : 0.37
% 2.59/1.42  Parsing              : 0.19
% 2.59/1.42  CNF conversion       : 0.02
% 2.59/1.42  Main loop            : 0.26
% 2.59/1.42  Inferencing          : 0.10
% 2.59/1.42  Reduction            : 0.09
% 2.59/1.42  Demodulation         : 0.06
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.05
% 2.59/1.42  Abstraction          : 0.02
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.66
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
