%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:49 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 111 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 212 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & ~ v1_zfmisc_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_269,plain,(
    ! [A_63,B_64] :
      ( v1_zfmisc_1(A_63)
      | k6_domain_1(A_63,B_64) != A_63
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_284,plain,
    ( v1_zfmisc_1('#skF_5')
    | k6_domain_1('#skF_5','#skF_6') != '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_269])).

tff(c_291,plain,(
    k6_domain_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_284])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [B_55,A_56] :
      ( v1_subset_1(B_55,A_56)
      | B_55 = A_56
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_160,plain,(
    ! [A_15,B_16] :
      ( v1_subset_1(A_15,B_16)
      | B_16 = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_179,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_179])).

tff(c_201,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_194])).

tff(c_40,plain,(
    ~ v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_202,plain,(
    ~ v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_40])).

tff(c_210,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_160,c_202])).

tff(c_211,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_6,B_39] :
      ( '#skF_1'(k1_tarski(A_6),B_39) = A_6
      | r1_tarski(k1_tarski(A_6),B_39) ) ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_217,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_82,c_211])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_4])).

tff(c_232,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_224])).

tff(c_238,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_232])).

tff(c_241,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_238])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_241])).

tff(c_244,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_247,plain,(
    k6_domain_1('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_201])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:40:38 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.40  
% 2.19/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.41  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.19/1.41  
% 2.19/1.41  %Foreground sorts:
% 2.19/1.41  
% 2.19/1.41  
% 2.19/1.41  %Background operators:
% 2.19/1.41  
% 2.19/1.41  
% 2.19/1.41  %Foreground operators:
% 2.19/1.41  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.19/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.19/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.41  
% 2.19/1.42  tff(f_89, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 2.19/1.42  tff(f_70, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.19/1.42  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.19/1.42  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.42  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.19/1.42  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.19/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.42  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.42  tff(c_46, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.42  tff(c_44, plain, (~v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.42  tff(c_42, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.42  tff(c_269, plain, (![A_63, B_64]: (v1_zfmisc_1(A_63) | k6_domain_1(A_63, B_64)!=A_63 | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.42  tff(c_284, plain, (v1_zfmisc_1('#skF_5') | k6_domain_1('#skF_5', '#skF_6')!='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_269])).
% 2.19/1.42  tff(c_291, plain, (k6_domain_1('#skF_5', '#skF_6')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_284])).
% 2.19/1.42  tff(c_22, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.42  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.42  tff(c_146, plain, (![B_55, A_56]: (v1_subset_1(B_55, A_56) | B_55=A_56 | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.19/1.42  tff(c_160, plain, (![A_15, B_16]: (v1_subset_1(A_15, B_16) | B_16=A_15 | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.19/1.42  tff(c_179, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.42  tff(c_194, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_179])).
% 2.19/1.42  tff(c_201, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_194])).
% 2.19/1.42  tff(c_40, plain, (~v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.42  tff(c_202, plain, (~v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_40])).
% 2.19/1.42  tff(c_210, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_160, c_202])).
% 2.19/1.42  tff(c_211, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_210])).
% 2.19/1.42  tff(c_73, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.42  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.42  tff(c_82, plain, (![A_6, B_39]: ('#skF_1'(k1_tarski(A_6), B_39)=A_6 | r1_tarski(k1_tarski(A_6), B_39))), inference(resolution, [status(thm)], [c_73, c_8])).
% 2.19/1.42  tff(c_217, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_82, c_211])).
% 2.19/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.42  tff(c_224, plain, (~r2_hidden('#skF_6', '#skF_5') | r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_217, c_4])).
% 2.19/1.42  tff(c_232, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_211, c_224])).
% 2.19/1.42  tff(c_238, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_232])).
% 2.19/1.42  tff(c_241, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_238])).
% 2.19/1.42  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_241])).
% 2.19/1.42  tff(c_244, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_210])).
% 2.19/1.42  tff(c_247, plain, (k6_domain_1('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_201])).
% 2.19/1.42  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_247])).
% 2.19/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.42  
% 2.19/1.42  Inference rules
% 2.19/1.42  ----------------------
% 2.19/1.42  #Ref     : 0
% 2.19/1.42  #Sup     : 53
% 2.19/1.42  #Fact    : 0
% 2.19/1.42  #Define  : 0
% 2.19/1.42  #Split   : 2
% 2.19/1.42  #Chain   : 0
% 2.19/1.42  #Close   : 0
% 2.19/1.42  
% 2.19/1.42  Ordering : KBO
% 2.19/1.42  
% 2.19/1.42  Simplification rules
% 2.19/1.42  ----------------------
% 2.19/1.42  #Subsume      : 3
% 2.19/1.42  #Demod        : 16
% 2.19/1.42  #Tautology    : 19
% 2.19/1.42  #SimpNegUnit  : 8
% 2.19/1.42  #BackRed      : 4
% 2.19/1.42  
% 2.19/1.42  #Partial instantiations: 0
% 2.19/1.42  #Strategies tried      : 1
% 2.19/1.42  
% 2.19/1.42  Timing (in seconds)
% 2.19/1.42  ----------------------
% 2.19/1.42  Preprocessing        : 0.43
% 2.19/1.42  Parsing              : 0.25
% 2.19/1.42  CNF conversion       : 0.02
% 2.19/1.42  Main loop            : 0.19
% 2.19/1.42  Inferencing          : 0.07
% 2.19/1.42  Reduction            : 0.06
% 2.19/1.42  Demodulation         : 0.04
% 2.19/1.42  BG Simplification    : 0.02
% 2.19/1.42  Subsumption          : 0.03
% 2.19/1.42  Abstraction          : 0.01
% 2.19/1.42  MUC search           : 0.00
% 2.19/1.42  Cooper               : 0.00
% 2.19/1.42  Total                : 0.64
% 2.19/1.42  Index Insertion      : 0.00
% 2.19/1.42  Index Deletion       : 0.00
% 2.19/1.42  Index Matching       : 0.00
% 2.19/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
