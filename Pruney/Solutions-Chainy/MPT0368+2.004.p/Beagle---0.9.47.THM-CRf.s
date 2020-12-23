%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 130 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 282 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_194,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_14] : k3_tarski(k1_zfmisc_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k3_tarski(B_28))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    ! [A_27,A_14] :
      ( r1_tarski(A_27,A_14)
      | ~ r2_hidden(A_27,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_61])).

tff(c_205,plain,(
    ! [B_53,A_14] :
      ( r1_tarski(B_53,A_14)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_194,c_64])).

tff(c_318,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_205])).

tff(c_339,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_318])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_360,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_339,c_12])).

tff(c_365,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_360])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_173])).

tff(c_55,plain,(
    ! [C_26] :
      ( r2_hidden(C_26,'#skF_4')
      | ~ m1_subset_1(C_26,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [C_26] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_34,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,'#skF_4')
      | ~ m1_subset_1(C_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_182,plain,(
    ! [C_19] :
      ( m1_subset_1(C_19,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_19,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_173])).

tff(c_224,plain,(
    ! [C_56] :
      ( m1_subset_1(C_56,'#skF_4')
      | ~ m1_subset_1(C_56,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_182])).

tff(c_233,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_193,c_224])).

tff(c_235,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_275,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_205])).

tff(c_296,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_275])).

tff(c_91,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [A_38,B_39] :
      ( ~ v1_xboole_0(A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_108,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [B_39,A_38] :
      ( B_39 = A_38
      | ~ r1_tarski(B_39,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_106,c_108])).

tff(c_299,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_296,c_117])).

tff(c_304,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_299])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_304])).

tff(c_308,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_710,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1('#skF_2'(A_102,B_103),A_102)
      | v1_xboole_0(A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_85,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_2'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_36,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_85])).

tff(c_730,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_710,c_90])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_308,c_365,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.37  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.47/1.37  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.47/1.37  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.47/1.37  tff(f_50, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.47/1.37  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.47/1.37  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.47/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.47/1.37  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.47/1.37  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.37  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.37  tff(c_30, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.37  tff(c_194, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.37  tff(c_20, plain, (![A_14]: (k3_tarski(k1_zfmisc_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.37  tff(c_61, plain, (![A_27, B_28]: (r1_tarski(A_27, k3_tarski(B_28)) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.37  tff(c_64, plain, (![A_27, A_14]: (r1_tarski(A_27, A_14) | ~r2_hidden(A_27, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_61])).
% 2.47/1.37  tff(c_205, plain, (![B_53, A_14]: (r1_tarski(B_53, A_14) | ~m1_subset_1(B_53, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_194, c_64])).
% 2.47/1.37  tff(c_318, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_30, c_205])).
% 2.47/1.37  tff(c_339, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_318])).
% 2.47/1.37  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.37  tff(c_360, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_339, c_12])).
% 2.47/1.37  tff(c_365, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_360])).
% 2.47/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_173, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.37  tff(c_193, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_173])).
% 2.47/1.37  tff(c_55, plain, (![C_26]: (r2_hidden(C_26, '#skF_4') | ~m1_subset_1(C_26, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_59, plain, (![C_26]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_26, '#skF_3'))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.47/1.37  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_59])).
% 2.47/1.37  tff(c_34, plain, (![C_19]: (r2_hidden(C_19, '#skF_4') | ~m1_subset_1(C_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.37  tff(c_182, plain, (![C_19]: (m1_subset_1(C_19, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(C_19, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_173])).
% 2.47/1.37  tff(c_224, plain, (![C_56]: (m1_subset_1(C_56, '#skF_4') | ~m1_subset_1(C_56, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_182])).
% 2.47/1.37  tff(c_233, plain, (m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_193, c_224])).
% 2.47/1.37  tff(c_235, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_233])).
% 2.47/1.37  tff(c_275, plain, (![B_62, A_63]: (r1_tarski(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(negUnitSimplification, [status(thm)], [c_30, c_205])).
% 2.47/1.37  tff(c_296, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_275])).
% 2.47/1.37  tff(c_91, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.37  tff(c_106, plain, (![A_38, B_39]: (~v1_xboole_0(A_38) | r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_91, c_2])).
% 2.47/1.37  tff(c_108, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.37  tff(c_117, plain, (![B_39, A_38]: (B_39=A_38 | ~r1_tarski(B_39, A_38) | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_106, c_108])).
% 2.47/1.37  tff(c_299, plain, ('#skF_3'='#skF_4' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_296, c_117])).
% 2.47/1.37  tff(c_304, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_299])).
% 2.47/1.37  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_304])).
% 2.47/1.37  tff(c_308, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_233])).
% 2.47/1.37  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.37  tff(c_710, plain, (![A_102, B_103]: (m1_subset_1('#skF_2'(A_102, B_103), A_102) | v1_xboole_0(A_102) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_10, c_173])).
% 2.47/1.37  tff(c_85, plain, (![A_36, B_37]: (~r2_hidden('#skF_2'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.37  tff(c_90, plain, (![A_36]: (r1_tarski(A_36, '#skF_4') | ~m1_subset_1('#skF_2'(A_36, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_85])).
% 2.47/1.37  tff(c_730, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_710, c_90])).
% 2.47/1.37  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_308, c_365, c_730])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 143
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 5
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 42
% 2.47/1.37  #Demod        : 19
% 2.47/1.37  #Tautology    : 28
% 2.47/1.37  #SimpNegUnit  : 30
% 2.47/1.37  #BackRed      : 0
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.28
% 2.47/1.37  Parsing              : 0.15
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.32
% 2.47/1.37  Inferencing          : 0.12
% 2.47/1.37  Reduction            : 0.08
% 2.47/1.37  Demodulation         : 0.05
% 2.47/1.37  BG Simplification    : 0.01
% 2.47/1.37  Subsumption          : 0.07
% 2.47/1.37  Abstraction          : 0.01
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.63
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
