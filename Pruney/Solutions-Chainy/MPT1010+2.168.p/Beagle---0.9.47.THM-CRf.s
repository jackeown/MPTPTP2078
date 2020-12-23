%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_60,axiom,(
    ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(f_58,axiom,(
    ! [A] : k3_relat_1(k1_tarski(k4_tarski(A,A))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_72,axiom,(
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

tff(c_38,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_102,plain,(
    ! [A_35,B_36] : k3_relat_1(k1_tarski(k4_tarski(A_35,B_36))) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_16] : k3_relat_1(k1_tarski(k4_tarski(A_16,A_16))) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_118,plain,(
    ! [B_37] : k2_tarski(B_37,B_37) = k1_tarski(B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_32])).

tff(c_28,plain,(
    ! [B_14,C_15] : k4_xboole_0(k1_tarski(B_14),k2_tarski(B_14,C_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    ! [B_37] : k4_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_28])).

tff(c_18,plain,(
    ! [B_12] : k4_xboole_0(k1_tarski(B_12),k1_tarski(B_12)) != k1_tarski(B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [B_12] : k1_tarski(B_12) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_18])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_305,plain,(
    ! [D_68,C_69,B_70,A_71] :
      ( r2_hidden(k1_funct_1(D_68,C_69),B_70)
      | k1_xboole_0 = B_70
      | ~ r2_hidden(C_69,A_71)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70)))
      | ~ v1_funct_2(D_68,A_71,B_70)
      | ~ v1_funct_1(D_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_318,plain,(
    ! [D_72,B_73] :
      ( r2_hidden(k1_funct_1(D_72,'#skF_5'),B_73)
      | k1_xboole_0 = B_73
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_73)))
      | ~ v1_funct_2(D_72,'#skF_3',B_73)
      | ~ v1_funct_1(D_72) ) ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_321,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_318])).

tff(c_324,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_321])).

tff(c_325,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_324])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_330,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_325,c_2])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:29:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.34  
% 2.09/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.09/1.34  
% 2.09/1.34  %Foreground sorts:
% 2.09/1.34  
% 2.09/1.34  
% 2.09/1.34  %Background operators:
% 2.09/1.34  
% 2.09/1.34  
% 2.09/1.34  %Foreground operators:
% 2.09/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.34  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.09/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.34  
% 2.35/1.35  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.35/1.35  tff(f_60, axiom, (![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 2.35/1.35  tff(f_58, axiom, (![A]: (k3_relat_1(k1_tarski(k4_tarski(A, A))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t208_relat_1)).
% 2.35/1.35  tff(f_56, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.35/1.35  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.35/1.35  tff(f_72, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.35/1.35  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.35/1.35  tff(c_38, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.35  tff(c_102, plain, (![A_35, B_36]: (k3_relat_1(k1_tarski(k4_tarski(A_35, B_36)))=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.35  tff(c_32, plain, (![A_16]: (k3_relat_1(k1_tarski(k4_tarski(A_16, A_16)))=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.35  tff(c_118, plain, (![B_37]: (k2_tarski(B_37, B_37)=k1_tarski(B_37))), inference(superposition, [status(thm), theory('equality')], [c_102, c_32])).
% 2.35/1.35  tff(c_28, plain, (![B_14, C_15]: (k4_xboole_0(k1_tarski(B_14), k2_tarski(B_14, C_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.35  tff(c_127, plain, (![B_37]: (k4_xboole_0(k1_tarski(B_37), k1_tarski(B_37))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_28])).
% 2.35/1.35  tff(c_18, plain, (![B_12]: (k4_xboole_0(k1_tarski(B_12), k1_tarski(B_12))!=k1_tarski(B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.35  tff(c_158, plain, (![B_12]: (k1_tarski(B_12)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_18])).
% 2.35/1.35  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.35  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.35  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.35  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.35  tff(c_305, plain, (![D_68, C_69, B_70, A_71]: (r2_hidden(k1_funct_1(D_68, C_69), B_70) | k1_xboole_0=B_70 | ~r2_hidden(C_69, A_71) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))) | ~v1_funct_2(D_68, A_71, B_70) | ~v1_funct_1(D_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.35/1.35  tff(c_318, plain, (![D_72, B_73]: (r2_hidden(k1_funct_1(D_72, '#skF_5'), B_73) | k1_xboole_0=B_73 | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_73))) | ~v1_funct_2(D_72, '#skF_3', B_73) | ~v1_funct_1(D_72))), inference(resolution, [status(thm)], [c_40, c_305])).
% 2.35/1.35  tff(c_321, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_318])).
% 2.35/1.35  tff(c_324, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_321])).
% 2.35/1.35  tff(c_325, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_158, c_324])).
% 2.35/1.35  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.35  tff(c_330, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_325, c_2])).
% 2.35/1.35  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_330])).
% 2.35/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.35  
% 2.35/1.35  Inference rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Ref     : 0
% 2.35/1.35  #Sup     : 62
% 2.35/1.35  #Fact    : 0
% 2.35/1.35  #Define  : 0
% 2.35/1.35  #Split   : 0
% 2.35/1.35  #Chain   : 0
% 2.35/1.35  #Close   : 0
% 2.35/1.35  
% 2.35/1.35  Ordering : KBO
% 2.35/1.35  
% 2.35/1.35  Simplification rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Subsume      : 1
% 2.35/1.35  #Demod        : 16
% 2.35/1.35  #Tautology    : 47
% 2.35/1.35  #SimpNegUnit  : 8
% 2.35/1.35  #BackRed      : 1
% 2.35/1.35  
% 2.35/1.35  #Partial instantiations: 0
% 2.35/1.35  #Strategies tried      : 1
% 2.35/1.35  
% 2.35/1.35  Timing (in seconds)
% 2.35/1.35  ----------------------
% 2.35/1.35  Preprocessing        : 0.33
% 2.35/1.35  Parsing              : 0.17
% 2.35/1.35  CNF conversion       : 0.02
% 2.35/1.36  Main loop            : 0.21
% 2.35/1.36  Inferencing          : 0.08
% 2.35/1.36  Reduction            : 0.07
% 2.35/1.36  Demodulation         : 0.05
% 2.35/1.36  BG Simplification    : 0.02
% 2.35/1.36  Subsumption          : 0.04
% 2.35/1.36  Abstraction          : 0.02
% 2.35/1.36  MUC search           : 0.00
% 2.35/1.36  Cooper               : 0.00
% 2.35/1.36  Total                : 0.57
% 2.35/1.36  Index Insertion      : 0.00
% 2.35/1.36  Index Deletion       : 0.00
% 2.35/1.36  Index Matching       : 0.00
% 2.35/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
