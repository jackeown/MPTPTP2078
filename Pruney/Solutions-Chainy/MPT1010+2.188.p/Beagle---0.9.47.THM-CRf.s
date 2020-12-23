%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 158 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_14] : m1_subset_1('#skF_3'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [B_42] : r1_tarski('#skF_3'(k1_zfmisc_1(B_42)),B_42) ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_110,plain,(
    '#skF_3'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_117,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_36,plain,(
    ! [C_20,B_19,A_18] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117,c_36])).

tff(c_133,plain,(
    ! [A_18] : ~ r2_hidden(A_18,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2139,plain,(
    ! [D_3568,C_3569,B_3570,A_3571] :
      ( r2_hidden(k1_funct_1(D_3568,C_3569),B_3570)
      | k1_xboole_0 = B_3570
      | ~ r2_hidden(C_3569,A_3571)
      | ~ m1_subset_1(D_3568,k1_zfmisc_1(k2_zfmisc_1(A_3571,B_3570)))
      | ~ v1_funct_2(D_3568,A_3571,B_3570)
      | ~ v1_funct_1(D_3568) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2382,plain,(
    ! [D_3910,B_3911] :
      ( r2_hidden(k1_funct_1(D_3910,'#skF_6'),B_3911)
      | k1_xboole_0 = B_3911
      | ~ m1_subset_1(D_3910,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3911)))
      | ~ v1_funct_2(D_3910,'#skF_4',B_3911)
      | ~ v1_funct_1(D_3910) ) ),
    inference(resolution,[status(thm)],[c_42,c_2139])).

tff(c_2395,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_2382])).

tff(c_2403,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2395])).

tff(c_2405,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2403])).

tff(c_24,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [D_28,A_29] : r2_hidden(D_28,k2_tarski(A_29,D_28)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_60])).

tff(c_2421,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2405,c_63])).

tff(c_2465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2421])).

tff(c_2466,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2403])).

tff(c_168,plain,(
    ! [D_55,B_56,A_57] :
      ( D_55 = B_56
      | D_55 = A_57
      | ~ r2_hidden(D_55,k2_tarski(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [D_55,A_8] :
      ( D_55 = A_8
      | D_55 = A_8
      | ~ r2_hidden(D_55,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_168])).

tff(c_2476,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2466,c_177])).

tff(c_2524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_2476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:38 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.61  
% 3.46/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.62  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.46/1.62  
% 3.46/1.62  %Foreground sorts:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Background operators:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Foreground operators:
% 3.46/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.46/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.46/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.62  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.62  
% 3.46/1.63  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.46/1.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.46/1.63  tff(f_48, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.46/1.63  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.63  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.46/1.63  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.46/1.63  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.46/1.63  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.46/1.63  tff(f_39, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.46/1.63  tff(c_40, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.46/1.63  tff(c_30, plain, (![A_14]: (m1_subset_1('#skF_3'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.63  tff(c_80, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.63  tff(c_105, plain, (![B_42]: (r1_tarski('#skF_3'(k1_zfmisc_1(B_42)), B_42))), inference(resolution, [status(thm)], [c_30, c_80])).
% 3.46/1.63  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.46/1.63  tff(c_110, plain, ('#skF_3'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_4])).
% 3.46/1.63  tff(c_117, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_30])).
% 3.46/1.63  tff(c_36, plain, (![C_20, B_19, A_18]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.63  tff(c_127, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_36])).
% 3.46/1.63  tff(c_133, plain, (![A_18]: (~r2_hidden(A_18, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 3.46/1.63  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.63  tff(c_46, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.63  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.63  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.63  tff(c_2139, plain, (![D_3568, C_3569, B_3570, A_3571]: (r2_hidden(k1_funct_1(D_3568, C_3569), B_3570) | k1_xboole_0=B_3570 | ~r2_hidden(C_3569, A_3571) | ~m1_subset_1(D_3568, k1_zfmisc_1(k2_zfmisc_1(A_3571, B_3570))) | ~v1_funct_2(D_3568, A_3571, B_3570) | ~v1_funct_1(D_3568))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.63  tff(c_2382, plain, (![D_3910, B_3911]: (r2_hidden(k1_funct_1(D_3910, '#skF_6'), B_3911) | k1_xboole_0=B_3911 | ~m1_subset_1(D_3910, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3911))) | ~v1_funct_2(D_3910, '#skF_4', B_3911) | ~v1_funct_1(D_3910))), inference(resolution, [status(thm)], [c_42, c_2139])).
% 3.46/1.63  tff(c_2395, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_2382])).
% 3.46/1.63  tff(c_2403, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2395])).
% 3.46/1.63  tff(c_2405, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2403])).
% 3.46/1.63  tff(c_24, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.63  tff(c_60, plain, (![D_28, A_29]: (r2_hidden(D_28, k2_tarski(A_29, D_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.63  tff(c_63, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_60])).
% 3.46/1.63  tff(c_2421, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2405, c_63])).
% 3.46/1.63  tff(c_2465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_2421])).
% 3.46/1.63  tff(c_2466, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_2403])).
% 3.46/1.63  tff(c_168, plain, (![D_55, B_56, A_57]: (D_55=B_56 | D_55=A_57 | ~r2_hidden(D_55, k2_tarski(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.63  tff(c_177, plain, (![D_55, A_8]: (D_55=A_8 | D_55=A_8 | ~r2_hidden(D_55, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_168])).
% 3.46/1.63  tff(c_2476, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_2466, c_177])).
% 3.46/1.63  tff(c_2524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_2476])).
% 3.46/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.63  
% 3.46/1.63  Inference rules
% 3.46/1.63  ----------------------
% 3.46/1.63  #Ref     : 0
% 3.46/1.63  #Sup     : 337
% 3.46/1.63  #Fact    : 8
% 3.46/1.63  #Define  : 0
% 3.79/1.63  #Split   : 7
% 3.79/1.63  #Chain   : 0
% 3.79/1.63  #Close   : 0
% 3.79/1.63  
% 3.79/1.63  Ordering : KBO
% 3.79/1.63  
% 3.79/1.63  Simplification rules
% 3.79/1.63  ----------------------
% 3.79/1.63  #Subsume      : 89
% 3.79/1.63  #Demod        : 61
% 3.79/1.63  #Tautology    : 95
% 3.79/1.63  #SimpNegUnit  : 13
% 3.79/1.63  #BackRed      : 4
% 3.79/1.63  
% 3.79/1.63  #Partial instantiations: 2745
% 3.79/1.63  #Strategies tried      : 1
% 3.79/1.63  
% 3.79/1.63  Timing (in seconds)
% 3.79/1.63  ----------------------
% 3.79/1.63  Preprocessing        : 0.31
% 3.79/1.63  Parsing              : 0.16
% 3.79/1.63  CNF conversion       : 0.02
% 3.79/1.63  Main loop            : 0.56
% 3.79/1.63  Inferencing          : 0.29
% 3.79/1.63  Reduction            : 0.13
% 3.79/1.63  Demodulation         : 0.09
% 3.79/1.63  BG Simplification    : 0.03
% 3.79/1.63  Subsumption          : 0.07
% 3.79/1.63  Abstraction          : 0.03
% 3.79/1.63  MUC search           : 0.00
% 3.79/1.63  Cooper               : 0.00
% 3.79/1.63  Total                : 0.89
% 3.79/1.63  Index Insertion      : 0.00
% 3.79/1.63  Index Deletion       : 0.00
% 3.79/1.63  Index Matching       : 0.00
% 3.79/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
