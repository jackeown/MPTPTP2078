%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   66 (  82 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 152 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_46,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_256,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3159,plain,(
    ! [A_252,B_253,B_254] :
      ( r2_hidden(A_252,B_253)
      | ~ r1_tarski(B_254,B_253)
      | v1_xboole_0(B_254)
      | ~ m1_subset_1(A_252,B_254) ) ),
    inference(resolution,[status(thm)],[c_38,c_256])).

tff(c_3197,plain,(
    ! [A_252] :
      ( r2_hidden(A_252,k2_relat_1('#skF_6'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_252,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_3159])).

tff(c_3199,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3197])).

tff(c_160,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_36,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    ! [A_42,A_17] :
      ( r1_tarski(A_42,A_17)
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ m1_subset_1(A_42,k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_85,c_22])).

tff(c_97,plain,(
    ! [A_44,A_45] :
      ( r1_tarski(A_44,A_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_45)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_89])).

tff(c_101,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_103,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_101,c_103])).

tff(c_181,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_170,c_112])).

tff(c_3209,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3199,c_181])).

tff(c_3216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3209])).

tff(c_3218,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3197])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_308,plain,(
    ! [B_74,A_75] :
      ( r1_xboole_0(k2_relat_1(B_74),A_75)
      | k10_relat_1(B_74,A_75) != k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3905,plain,(
    ! [A_286,A_287,B_288] :
      ( r1_xboole_0(A_286,A_287)
      | ~ r1_tarski(A_286,k2_relat_1(B_288))
      | k10_relat_1(B_288,A_287) != k1_xboole_0
      | ~ v1_relat_1(B_288) ) ),
    inference(resolution,[status(thm)],[c_308,c_18])).

tff(c_3940,plain,(
    ! [A_287] :
      ( r1_xboole_0('#skF_5',A_287)
      | k10_relat_1('#skF_6',A_287) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_3905])).

tff(c_3959,plain,(
    ! [A_289] :
      ( r1_xboole_0('#skF_5',A_289)
      | k10_relat_1('#skF_6',A_289) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3940])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_xboole_0(B_16,A_15)
      | ~ r1_tarski(B_16,A_15)
      | v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3964,plain,(
    ! [A_289] :
      ( ~ r1_tarski('#skF_5',A_289)
      | v1_xboole_0('#skF_5')
      | k10_relat_1('#skF_6',A_289) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3959,c_20])).

tff(c_3969,plain,(
    ! [A_290] :
      ( ~ r1_tarski('#skF_5',A_290)
      | k10_relat_1('#skF_6',A_290) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3218,c_3964])).

tff(c_3980,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_3969])).

tff(c_3986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:19:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.82  
% 4.70/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.70/1.82  
% 4.70/1.82  %Foreground sorts:
% 4.70/1.82  
% 4.70/1.82  
% 4.70/1.82  %Background operators:
% 4.70/1.82  
% 4.70/1.82  
% 4.70/1.82  %Foreground operators:
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.70/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.70/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.70/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.70/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.70/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.82  
% 4.70/1.84  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 4.70/1.84  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.70/1.84  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.70/1.84  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.70/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.70/1.84  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.70/1.84  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.70/1.84  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.70/1.84  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 4.70/1.84  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.70/1.84  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.70/1.84  tff(c_46, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.84  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.70/1.84  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.84  tff(c_48, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.84  tff(c_38, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | v1_xboole_0(B_25) | ~m1_subset_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.84  tff(c_256, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.84  tff(c_3159, plain, (![A_252, B_253, B_254]: (r2_hidden(A_252, B_253) | ~r1_tarski(B_254, B_253) | v1_xboole_0(B_254) | ~m1_subset_1(A_252, B_254))), inference(resolution, [status(thm)], [c_38, c_256])).
% 4.70/1.84  tff(c_3197, plain, (![A_252]: (r2_hidden(A_252, k2_relat_1('#skF_6')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_252, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_3159])).
% 4.70/1.84  tff(c_3199, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3197])).
% 4.70/1.84  tff(c_160, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.84  tff(c_170, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_160, c_2])).
% 4.70/1.84  tff(c_36, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.70/1.84  tff(c_34, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.70/1.84  tff(c_85, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.84  tff(c_22, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.70/1.84  tff(c_89, plain, (![A_42, A_17]: (r1_tarski(A_42, A_17) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~m1_subset_1(A_42, k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_85, c_22])).
% 4.70/1.84  tff(c_97, plain, (![A_44, A_45]: (r1_tarski(A_44, A_45) | ~m1_subset_1(A_44, k1_zfmisc_1(A_45)))), inference(negUnitSimplification, [status(thm)], [c_34, c_89])).
% 4.70/1.84  tff(c_101, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(resolution, [status(thm)], [c_36, c_97])).
% 4.70/1.84  tff(c_103, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.70/1.84  tff(c_112, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_101, c_103])).
% 4.70/1.84  tff(c_181, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_170, c_112])).
% 4.70/1.84  tff(c_3209, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3199, c_181])).
% 4.70/1.84  tff(c_3216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3209])).
% 4.70/1.84  tff(c_3218, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_3197])).
% 4.70/1.84  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.84  tff(c_308, plain, (![B_74, A_75]: (r1_xboole_0(k2_relat_1(B_74), A_75) | k10_relat_1(B_74, A_75)!=k1_xboole_0 | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.84  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.70/1.84  tff(c_3905, plain, (![A_286, A_287, B_288]: (r1_xboole_0(A_286, A_287) | ~r1_tarski(A_286, k2_relat_1(B_288)) | k10_relat_1(B_288, A_287)!=k1_xboole_0 | ~v1_relat_1(B_288))), inference(resolution, [status(thm)], [c_308, c_18])).
% 4.70/1.84  tff(c_3940, plain, (![A_287]: (r1_xboole_0('#skF_5', A_287) | k10_relat_1('#skF_6', A_287)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_3905])).
% 4.70/1.84  tff(c_3959, plain, (![A_289]: (r1_xboole_0('#skF_5', A_289) | k10_relat_1('#skF_6', A_289)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3940])).
% 4.70/1.84  tff(c_20, plain, (![B_16, A_15]: (~r1_xboole_0(B_16, A_15) | ~r1_tarski(B_16, A_15) | v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.70/1.84  tff(c_3964, plain, (![A_289]: (~r1_tarski('#skF_5', A_289) | v1_xboole_0('#skF_5') | k10_relat_1('#skF_6', A_289)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3959, c_20])).
% 4.70/1.84  tff(c_3969, plain, (![A_290]: (~r1_tarski('#skF_5', A_290) | k10_relat_1('#skF_6', A_290)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3218, c_3964])).
% 4.70/1.84  tff(c_3980, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_3969])).
% 4.70/1.84  tff(c_3986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_3980])).
% 4.70/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.84  
% 4.70/1.84  Inference rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Ref     : 0
% 4.70/1.84  #Sup     : 893
% 4.70/1.84  #Fact    : 0
% 4.70/1.84  #Define  : 0
% 4.70/1.84  #Split   : 10
% 4.70/1.84  #Chain   : 0
% 4.70/1.84  #Close   : 0
% 4.70/1.84  
% 4.70/1.84  Ordering : KBO
% 4.70/1.84  
% 4.70/1.84  Simplification rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Subsume      : 295
% 4.70/1.84  #Demod        : 374
% 4.70/1.84  #Tautology    : 318
% 4.70/1.84  #SimpNegUnit  : 80
% 4.70/1.84  #BackRed      : 32
% 4.70/1.84  
% 4.70/1.84  #Partial instantiations: 0
% 4.70/1.84  #Strategies tried      : 1
% 4.70/1.84  
% 4.70/1.84  Timing (in seconds)
% 4.70/1.84  ----------------------
% 4.70/1.84  Preprocessing        : 0.31
% 4.70/1.84  Parsing              : 0.16
% 4.70/1.84  CNF conversion       : 0.02
% 4.70/1.84  Main loop            : 0.78
% 4.70/1.84  Inferencing          : 0.27
% 4.70/1.84  Reduction            : 0.23
% 4.70/1.84  Demodulation         : 0.15
% 4.70/1.84  BG Simplification    : 0.03
% 4.70/1.84  Subsumption          : 0.19
% 4.70/1.84  Abstraction          : 0.03
% 4.70/1.84  MUC search           : 0.00
% 4.70/1.84  Cooper               : 0.00
% 4.70/1.84  Total                : 1.12
% 4.70/1.84  Index Insertion      : 0.00
% 4.70/1.84  Index Deletion       : 0.00
% 4.70/1.84  Index Matching       : 0.00
% 4.70/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
