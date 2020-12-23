%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 129 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,(
    ! [D_60,A_61,B_62,C_63] :
      ( k1_funct_1(D_60,'#skF_2'(A_61,B_62,C_63,D_60)) = C_63
      | ~ r2_hidden(C_63,k2_relset_1(A_61,B_62,D_60))
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_60,A_61,B_62)
      | ~ v1_funct_1(D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) = '#skF_3'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_154,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_149])).

tff(c_68,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( r2_hidden('#skF_2'(A_36,B_37,C_38,D_39),A_36)
      | ~ r2_hidden(C_38,k2_relset_1(A_36,B_37,D_39))
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(D_39,A_36,B_37)
      | ~ v1_funct_1(D_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    ! [C_38] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_38,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_38,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_91,plain,(
    ! [C_44] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_44,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_44,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_73])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [A_32,C_33,B_34] :
      ( m1_subset_1(A_32,C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_32,B_7,A_6] :
      ( m1_subset_1(A_32,B_7)
      | ~ r2_hidden(A_32,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_224,plain,(
    ! [C_81,B_82] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_81,'#skF_6'),B_82)
      | ~ r1_tarski('#skF_4',B_82)
      | ~ r2_hidden(C_81,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_91,c_65])).

tff(c_240,plain,(
    ! [B_83] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6'),B_83)
      | ~ r1_tarski('#skF_4',B_83) ) ),
    inference(resolution,[status(thm)],[c_20,c_224])).

tff(c_18,plain,(
    ! [E_17] :
      ( k1_funct_1('#skF_6',E_17) != '#skF_3'
      | ~ m1_subset_1(E_17,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_250,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) != '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_154,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:12:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.15/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.26  
% 2.29/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.27  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.29/1.27  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.29/1.27  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.29/1.27  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.29/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.27  tff(c_39, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.27  tff(c_44, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.29/1.27  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.27  tff(c_24, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.27  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.27  tff(c_20, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.27  tff(c_141, plain, (![D_60, A_61, B_62, C_63]: (k1_funct_1(D_60, '#skF_2'(A_61, B_62, C_63, D_60))=C_63 | ~r2_hidden(C_63, k2_relset_1(A_61, B_62, D_60)) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_60, A_61, B_62) | ~v1_funct_1(D_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.29/1.27  tff(c_149, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))='#skF_3' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_141])).
% 2.29/1.27  tff(c_154, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_149])).
% 2.29/1.27  tff(c_68, plain, (![A_36, B_37, C_38, D_39]: (r2_hidden('#skF_2'(A_36, B_37, C_38, D_39), A_36) | ~r2_hidden(C_38, k2_relset_1(A_36, B_37, D_39)) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(D_39, A_36, B_37) | ~v1_funct_1(D_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.29/1.27  tff(c_73, plain, (![C_38]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_38, '#skF_6'), '#skF_4') | ~r2_hidden(C_38, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.29/1.27  tff(c_91, plain, (![C_44]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_44, '#skF_6'), '#skF_4') | ~r2_hidden(C_44, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_73])).
% 2.29/1.27  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.29/1.27  tff(c_60, plain, (![A_32, C_33, B_34]: (m1_subset_1(A_32, C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.27  tff(c_65, plain, (![A_32, B_7, A_6]: (m1_subset_1(A_32, B_7) | ~r2_hidden(A_32, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.29/1.27  tff(c_224, plain, (![C_81, B_82]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_81, '#skF_6'), B_82) | ~r1_tarski('#skF_4', B_82) | ~r2_hidden(C_81, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_91, c_65])).
% 2.29/1.27  tff(c_240, plain, (![B_83]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'), B_83) | ~r1_tarski('#skF_4', B_83))), inference(resolution, [status(thm)], [c_20, c_224])).
% 2.29/1.27  tff(c_18, plain, (![E_17]: (k1_funct_1('#skF_6', E_17)!='#skF_3' | ~m1_subset_1(E_17, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.27  tff(c_250, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))!='#skF_3' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_240, c_18])).
% 2.29/1.27  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_154, c_250])).
% 2.29/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.27  
% 2.29/1.27  Inference rules
% 2.29/1.27  ----------------------
% 2.29/1.27  #Ref     : 0
% 2.29/1.27  #Sup     : 54
% 2.29/1.27  #Fact    : 0
% 2.29/1.27  #Define  : 0
% 2.29/1.27  #Split   : 1
% 2.29/1.27  #Chain   : 0
% 2.29/1.27  #Close   : 0
% 2.29/1.27  
% 2.29/1.27  Ordering : KBO
% 2.29/1.27  
% 2.29/1.27  Simplification rules
% 2.29/1.27  ----------------------
% 2.29/1.27  #Subsume      : 3
% 2.29/1.27  #Demod        : 8
% 2.29/1.27  #Tautology    : 5
% 2.29/1.27  #SimpNegUnit  : 0
% 2.29/1.27  #BackRed      : 0
% 2.29/1.27  
% 2.29/1.27  #Partial instantiations: 0
% 2.29/1.27  #Strategies tried      : 1
% 2.29/1.27  
% 2.29/1.27  Timing (in seconds)
% 2.29/1.27  ----------------------
% 2.29/1.27  Preprocessing        : 0.28
% 2.29/1.27  Parsing              : 0.15
% 2.29/1.27  CNF conversion       : 0.02
% 2.29/1.27  Main loop            : 0.25
% 2.29/1.27  Inferencing          : 0.10
% 2.29/1.27  Reduction            : 0.06
% 2.29/1.27  Demodulation         : 0.05
% 2.29/1.27  BG Simplification    : 0.01
% 2.29/1.27  Subsumption          : 0.06
% 2.29/1.27  Abstraction          : 0.01
% 2.29/1.27  MUC search           : 0.00
% 2.29/1.27  Cooper               : 0.00
% 2.29/1.27  Total                : 0.55
% 2.29/1.27  Index Insertion      : 0.00
% 2.29/1.27  Index Deletion       : 0.00
% 2.29/1.27  Index Matching       : 0.00
% 2.29/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
