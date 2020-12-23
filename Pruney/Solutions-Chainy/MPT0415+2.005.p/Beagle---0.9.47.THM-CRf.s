%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 203 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 333 expanded)
%              Number of equality atoms :   17 ( 124 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_41])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_34])).

tff(c_32,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_47,plain,(
    k7_setfam_1('#skF_4','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_32])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ! [A_39,B_40] :
      ( k7_setfam_1(A_39,k7_setfam_1(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    k7_setfam_1('#skF_4',k7_setfam_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_89,plain,(
    k7_setfam_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_87])).

tff(c_95,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k7_setfam_1(A_42,B_43),k1_zfmisc_1(k1_zfmisc_1(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_105,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_95])).

tff(c_110,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_105])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( m1_subset_1(A_23,C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_127,plain,(
    ! [A_48,A_49,B_50] :
      ( m1_subset_1(A_48,k1_zfmisc_1(A_49))
      | ~ r2_hidden(A_48,k7_setfam_1(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(resolution,[status(thm)],[c_95,c_30])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_56,B_57)),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | v1_xboole_0(k7_setfam_1(A_56,B_57)) ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_175,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | v1_xboole_0(k7_setfam_1('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_164])).

tff(c_183,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_110,c_175])).

tff(c_186,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_6])).

tff(c_191,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_186,c_46])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_191])).

tff(c_198,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_73,plain,(
    ! [A_33,C_34,B_35] :
      ( m1_subset_1(A_33,C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_33,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_465,plain,(
    ! [A_85,D_86,B_87] :
      ( r2_hidden(k3_subset_1(A_85,D_86),B_87)
      | ~ r2_hidden(D_86,k7_setfam_1(A_85,B_87))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(k7_setfam_1(A_85,B_87),k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_471,plain,(
    ! [D_86] :
      ( r2_hidden(k3_subset_1('#skF_4',D_86),'#skF_2')
      | ~ r2_hidden(D_86,k7_setfam_1('#skF_4','#skF_2'))
      | ~ m1_subset_1(D_86,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_465])).

tff(c_479,plain,(
    ! [D_88] :
      ( r2_hidden(k3_subset_1('#skF_4',D_88),'#skF_2')
      | ~ r2_hidden(D_88,'#skF_5')
      | ~ m1_subset_1(D_88,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_36,c_89,c_471])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_488,plain,(
    ! [D_88] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(D_88,'#skF_5')
      | ~ m1_subset_1(D_88,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_479,c_2])).

tff(c_497,plain,(
    ! [D_89] :
      ( ~ r2_hidden(D_89,'#skF_5')
      | ~ m1_subset_1(D_89,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_488])).

tff(c_525,plain,(
    ! [A_90] : ~ r2_hidden(A_90,'#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_497])).

tff(c_529,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_525])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:39:44 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.37  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.54/1.37  
% 2.54/1.37  %Foreground sorts:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Background operators:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Foreground operators:
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.37  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.54/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.54/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.37  
% 2.54/1.38  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.54/1.38  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.54/1.38  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.54/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.54/1.38  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.54/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.54/1.38  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.54/1.38  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.54/1.38  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.38  tff(c_41, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.38  tff(c_45, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_41])).
% 2.54/1.38  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.38  tff(c_48, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_34])).
% 2.54/1.38  tff(c_32, plain, (k7_setfam_1('#skF_4', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.38  tff(c_47, plain, (k7_setfam_1('#skF_4', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_32])).
% 2.54/1.38  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.38  tff(c_85, plain, (![A_39, B_40]: (k7_setfam_1(A_39, k7_setfam_1(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.38  tff(c_87, plain, (k7_setfam_1('#skF_4', k7_setfam_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_36, c_85])).
% 2.54/1.38  tff(c_89, plain, (k7_setfam_1('#skF_4', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_87])).
% 2.54/1.38  tff(c_95, plain, (![A_42, B_43]: (m1_subset_1(k7_setfam_1(A_42, B_43), k1_zfmisc_1(k1_zfmisc_1(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.38  tff(c_105, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_47, c_95])).
% 2.54/1.38  tff(c_110, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_105])).
% 2.54/1.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.38  tff(c_30, plain, (![A_23, C_25, B_24]: (m1_subset_1(A_23, C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(C_25)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.54/1.38  tff(c_127, plain, (![A_48, A_49, B_50]: (m1_subset_1(A_48, k1_zfmisc_1(A_49)) | ~r2_hidden(A_48, k7_setfam_1(A_49, B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(resolution, [status(thm)], [c_95, c_30])).
% 2.54/1.38  tff(c_164, plain, (![A_56, B_57]: (m1_subset_1('#skF_1'(k7_setfam_1(A_56, B_57)), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))) | v1_xboole_0(k7_setfam_1(A_56, B_57)))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.54/1.38  tff(c_175, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | v1_xboole_0(k7_setfam_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_164])).
% 2.54/1.38  tff(c_183, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_110, c_175])).
% 2.54/1.38  tff(c_186, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_183])).
% 2.54/1.38  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.38  tff(c_46, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_6])).
% 2.54/1.38  tff(c_191, plain, ('#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_186, c_46])).
% 2.54/1.38  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_191])).
% 2.54/1.38  tff(c_198, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_183])).
% 2.54/1.38  tff(c_73, plain, (![A_33, C_34, B_35]: (m1_subset_1(A_33, C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.54/1.38  tff(c_76, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_33, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_73])).
% 2.54/1.38  tff(c_465, plain, (![A_85, D_86, B_87]: (r2_hidden(k3_subset_1(A_85, D_86), B_87) | ~r2_hidden(D_86, k7_setfam_1(A_85, B_87)) | ~m1_subset_1(D_86, k1_zfmisc_1(A_85)) | ~m1_subset_1(k7_setfam_1(A_85, B_87), k1_zfmisc_1(k1_zfmisc_1(A_85))) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.38  tff(c_471, plain, (![D_86]: (r2_hidden(k3_subset_1('#skF_4', D_86), '#skF_2') | ~r2_hidden(D_86, k7_setfam_1('#skF_4', '#skF_2')) | ~m1_subset_1(D_86, k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_89, c_465])).
% 2.54/1.38  tff(c_479, plain, (![D_88]: (r2_hidden(k3_subset_1('#skF_4', D_88), '#skF_2') | ~r2_hidden(D_88, '#skF_5') | ~m1_subset_1(D_88, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_36, c_89, c_471])).
% 2.54/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.38  tff(c_488, plain, (![D_88]: (~v1_xboole_0('#skF_2') | ~r2_hidden(D_88, '#skF_5') | ~m1_subset_1(D_88, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_479, c_2])).
% 2.54/1.38  tff(c_497, plain, (![D_89]: (~r2_hidden(D_89, '#skF_5') | ~m1_subset_1(D_89, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_488])).
% 2.54/1.38  tff(c_525, plain, (![A_90]: (~r2_hidden(A_90, '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_497])).
% 2.54/1.38  tff(c_529, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_525])).
% 2.54/1.38  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_529])).
% 2.54/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  Inference rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Ref     : 0
% 2.54/1.38  #Sup     : 116
% 2.54/1.38  #Fact    : 0
% 2.54/1.38  #Define  : 0
% 2.54/1.38  #Split   : 4
% 2.54/1.38  #Chain   : 0
% 2.54/1.38  #Close   : 0
% 2.54/1.38  
% 2.54/1.38  Ordering : KBO
% 2.54/1.38  
% 2.54/1.38  Simplification rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Subsume      : 21
% 2.54/1.38  #Demod        : 88
% 2.54/1.38  #Tautology    : 40
% 2.54/1.38  #SimpNegUnit  : 7
% 2.54/1.38  #BackRed      : 6
% 2.54/1.38  
% 2.54/1.38  #Partial instantiations: 0
% 2.54/1.38  #Strategies tried      : 1
% 2.54/1.38  
% 2.54/1.38  Timing (in seconds)
% 2.54/1.38  ----------------------
% 2.54/1.39  Preprocessing        : 0.30
% 2.54/1.39  Parsing              : 0.16
% 2.54/1.39  CNF conversion       : 0.02
% 2.54/1.39  Main loop            : 0.30
% 2.54/1.39  Inferencing          : 0.11
% 2.54/1.39  Reduction            : 0.08
% 2.54/1.39  Demodulation         : 0.06
% 2.54/1.39  BG Simplification    : 0.02
% 2.54/1.39  Subsumption          : 0.06
% 2.54/1.39  Abstraction          : 0.02
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.63
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
