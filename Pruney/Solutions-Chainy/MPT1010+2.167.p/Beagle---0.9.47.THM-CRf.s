%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 169 expanded)
%              Number of equality atoms :   19 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_28,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [D_46,C_47,B_48,A_49] :
      ( r2_hidden(k1_funct_1(D_46,C_47),B_48)
      | k1_xboole_0 = B_48
      | ~ r2_hidden(C_47,A_49)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48)))
      | ~ v1_funct_2(D_46,A_49,B_48)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [D_52,B_53] :
      ( r2_hidden(k1_funct_1(D_52,'#skF_5'),B_53)
      | k1_xboole_0 = B_53
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_53)))
      | ~ v1_funct_2(D_52,'#skF_3',B_53)
      | ~ v1_funct_1(D_52) ) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_141,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_144,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_141])).

tff(c_145,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_24,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),B_16) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_162,plain,(
    ! [B_16] : k2_xboole_0(k1_xboole_0,B_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_24])).

tff(c_171,plain,(
    ! [B_16] : k1_xboole_0 != B_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_162])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_145])).

tff(c_177,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_177,c_6])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.94/1.29  
% 1.94/1.29  %Foreground sorts:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Background operators:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Foreground operators:
% 1.94/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.29  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.29  
% 1.94/1.30  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 1.94/1.30  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.30  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.94/1.30  tff(f_59, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.94/1.30  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.94/1.30  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.94/1.30  tff(c_28, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.30  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.30  tff(c_55, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.30  tff(c_59, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_55])).
% 1.94/1.30  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.30  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.30  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.30  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.30  tff(c_124, plain, (![D_46, C_47, B_48, A_49]: (r2_hidden(k1_funct_1(D_46, C_47), B_48) | k1_xboole_0=B_48 | ~r2_hidden(C_47, A_49) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))) | ~v1_funct_2(D_46, A_49, B_48) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.30  tff(c_138, plain, (![D_52, B_53]: (r2_hidden(k1_funct_1(D_52, '#skF_5'), B_53) | k1_xboole_0=B_53 | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_53))) | ~v1_funct_2(D_52, '#skF_3', B_53) | ~v1_funct_1(D_52))), inference(resolution, [status(thm)], [c_30, c_124])).
% 1.94/1.30  tff(c_141, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_138])).
% 1.94/1.30  tff(c_144, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_141])).
% 1.94/1.30  tff(c_145, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144])).
% 1.94/1.30  tff(c_24, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.30  tff(c_162, plain, (![B_16]: (k2_xboole_0(k1_xboole_0, B_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_24])).
% 1.94/1.30  tff(c_171, plain, (![B_16]: (k1_xboole_0!=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_162])).
% 1.94/1.30  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_145])).
% 1.94/1.30  tff(c_177, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_144])).
% 1.94/1.30  tff(c_6, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.30  tff(c_184, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_177, c_6])).
% 1.94/1.30  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_184])).
% 1.94/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.30  
% 1.94/1.30  Inference rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Ref     : 0
% 1.94/1.30  #Sup     : 32
% 1.94/1.30  #Fact    : 0
% 1.94/1.30  #Define  : 0
% 1.94/1.30  #Split   : 1
% 1.94/1.30  #Chain   : 0
% 1.94/1.30  #Close   : 0
% 1.94/1.30  
% 1.94/1.30  Ordering : KBO
% 1.94/1.30  
% 1.94/1.30  Simplification rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Subsume      : 1
% 1.94/1.30  #Demod        : 15
% 1.94/1.30  #Tautology    : 16
% 1.94/1.30  #SimpNegUnit  : 4
% 1.94/1.30  #BackRed      : 5
% 1.94/1.30  
% 1.94/1.30  #Partial instantiations: 0
% 1.94/1.30  #Strategies tried      : 1
% 1.94/1.30  
% 1.94/1.30  Timing (in seconds)
% 1.94/1.30  ----------------------
% 1.94/1.30  Preprocessing        : 0.33
% 1.94/1.30  Parsing              : 0.17
% 1.94/1.30  CNF conversion       : 0.02
% 1.94/1.30  Main loop            : 0.17
% 1.94/1.30  Inferencing          : 0.06
% 1.94/1.30  Reduction            : 0.05
% 1.94/1.30  Demodulation         : 0.04
% 1.94/1.30  BG Simplification    : 0.01
% 1.94/1.30  Subsumption          : 0.04
% 1.94/1.30  Abstraction          : 0.01
% 1.94/1.30  MUC search           : 0.00
% 1.94/1.30  Cooper               : 0.00
% 1.94/1.30  Total                : 0.52
% 1.94/1.30  Index Insertion      : 0.00
% 1.94/1.30  Index Deletion       : 0.00
% 1.94/1.30  Index Matching       : 0.00
% 1.94/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
