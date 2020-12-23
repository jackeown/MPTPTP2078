%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 107 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 233 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_71,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    ! [B_39,A_10] :
      ( r1_tarski(B_39,A_10)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_98,c_16])).

tff(c_115,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_106])).

tff(c_124,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_xboole_0(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_150,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_52,plain,(
    ! [C_27] :
      ( r2_hidden(C_27,'#skF_6')
      | ~ m1_subset_1(C_27,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [C_27] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_27,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_57,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_40,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,'#skF_6')
      | ~ m1_subset_1(C_19,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_139,plain,(
    ! [C_19] :
      ( m1_subset_1(C_19,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_19,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_163,plain,(
    ! [C_47] :
      ( m1_subset_1(C_47,'#skF_6')
      | ~ m1_subset_1(C_47,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_139])).

tff(c_172,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_163])).

tff(c_174,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_202,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),B_54)
      | ~ r2_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_224,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_xboole_0(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_229,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_224])).

tff(c_232,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_124,c_229])).

tff(c_238,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_232])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_238])).

tff(c_242,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_267,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),B_65)
      | ~ r2_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_355,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_2'(A_76,B_77),B_77)
      | v1_xboole_0(B_77)
      | ~ r2_xboole_0(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_267,c_28])).

tff(c_87,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_2'(A_37,B_38),A_37)
      | ~ r2_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [B_38] :
      ( ~ r2_xboole_0('#skF_6',B_38)
      | ~ m1_subset_1('#skF_2'('#skF_6',B_38),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_363,plain,
    ( v1_xboole_0('#skF_5')
    | ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_355,c_97])).

tff(c_376,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_363])).

tff(c_383,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_386,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_383])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.13/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.26  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.13/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.26  
% 2.13/1.27  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.13/1.27  tff(f_71, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.13/1.27  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.13/1.27  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.13/1.27  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.13/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.27  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.13/1.27  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.27  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.27  tff(c_36, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.27  tff(c_98, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.27  tff(c_16, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.27  tff(c_106, plain, (![B_39, A_10]: (r1_tarski(B_39, A_10) | ~m1_subset_1(B_39, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_98, c_16])).
% 2.13/1.27  tff(c_115, plain, (![B_41, A_42]: (r1_tarski(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_36, c_106])).
% 2.13/1.27  tff(c_124, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_115])).
% 2.13/1.27  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.27  tff(c_130, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.27  tff(c_150, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_130])).
% 2.13/1.27  tff(c_52, plain, (![C_27]: (r2_hidden(C_27, '#skF_6') | ~m1_subset_1(C_27, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.27  tff(c_56, plain, (![C_27]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(C_27, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.13/1.27  tff(c_57, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 2.13/1.27  tff(c_40, plain, (![C_19]: (r2_hidden(C_19, '#skF_6') | ~m1_subset_1(C_19, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.27  tff(c_139, plain, (![C_19]: (m1_subset_1(C_19, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(C_19, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_130])).
% 2.13/1.27  tff(c_163, plain, (![C_47]: (m1_subset_1(C_47, '#skF_6') | ~m1_subset_1(C_47, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_57, c_139])).
% 2.13/1.27  tff(c_172, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_150, c_163])).
% 2.13/1.27  tff(c_174, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_172])).
% 2.13/1.27  tff(c_202, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), B_54) | ~r2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.27  tff(c_224, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | ~r2_xboole_0(A_57, B_56))), inference(resolution, [status(thm)], [c_202, c_2])).
% 2.13/1.27  tff(c_229, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~r1_tarski(A_59, B_58))), inference(resolution, [status(thm)], [c_6, c_224])).
% 2.13/1.27  tff(c_232, plain, (~v1_xboole_0('#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_124, c_229])).
% 2.13/1.27  tff(c_238, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_232])).
% 2.13/1.27  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_238])).
% 2.13/1.27  tff(c_242, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_172])).
% 2.13/1.27  tff(c_267, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), B_65) | ~r2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.27  tff(c_28, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.27  tff(c_355, plain, (![A_76, B_77]: (m1_subset_1('#skF_2'(A_76, B_77), B_77) | v1_xboole_0(B_77) | ~r2_xboole_0(A_76, B_77))), inference(resolution, [status(thm)], [c_267, c_28])).
% 2.13/1.27  tff(c_87, plain, (![A_37, B_38]: (~r2_hidden('#skF_2'(A_37, B_38), A_37) | ~r2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.27  tff(c_97, plain, (![B_38]: (~r2_xboole_0('#skF_6', B_38) | ~m1_subset_1('#skF_2'('#skF_6', B_38), '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.13/1.27  tff(c_363, plain, (v1_xboole_0('#skF_5') | ~r2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_355, c_97])).
% 2.13/1.27  tff(c_376, plain, (~r2_xboole_0('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_242, c_363])).
% 2.13/1.27  tff(c_383, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_376])).
% 2.13/1.27  tff(c_386, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_383])).
% 2.13/1.27  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_386])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 64
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 2
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 18
% 2.13/1.27  #Demod        : 5
% 2.13/1.27  #Tautology    : 16
% 2.13/1.27  #SimpNegUnit  : 15
% 2.13/1.27  #BackRed      : 0
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.29
% 2.13/1.28  Parsing              : 0.15
% 2.13/1.28  CNF conversion       : 0.02
% 2.13/1.28  Main loop            : 0.22
% 2.13/1.28  Inferencing          : 0.09
% 2.13/1.28  Reduction            : 0.05
% 2.13/1.28  Demodulation         : 0.03
% 2.13/1.28  BG Simplification    : 0.02
% 2.13/1.28  Subsumption          : 0.04
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.53
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
