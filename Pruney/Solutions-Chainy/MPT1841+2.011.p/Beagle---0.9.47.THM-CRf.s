%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:29 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 116 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_752,plain,(
    ! [A_98,B_99] :
      ( k6_domain_1(A_98,B_99) = k1_tarski(B_99)
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_761,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_752])).

tff(c_766,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_761])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_767,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_38])).

tff(c_782,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k6_domain_1(A_106,B_107),k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_107,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_796,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_782])).

tff(c_802,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_796])).

tff(c_803,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_802])).

tff(c_1566,plain,(
    ! [B_159,A_160] :
      ( ~ v1_subset_1(B_159,A_160)
      | v1_xboole_0(B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_160))
      | ~ v1_zfmisc_1(A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1575,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_803,c_1566])).

tff(c_1593,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_767,c_1575])).

tff(c_1594,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1593])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1602,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1594,c_2])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_1625,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_59])).

tff(c_1638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.54  
% 3.10/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.54  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.10/1.54  
% 3.10/1.54  %Foreground sorts:
% 3.10/1.54  
% 3.10/1.54  
% 3.10/1.54  %Background operators:
% 3.10/1.54  
% 3.10/1.54  
% 3.10/1.54  %Foreground operators:
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.54  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.10/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.54  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.10/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.54  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.10/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.54  
% 3.44/1.55  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.44/1.55  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.55  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.44/1.55  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.44/1.55  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.44/1.55  tff(f_90, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.44/1.55  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.44/1.55  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.44/1.55  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.44/1.55  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.55  tff(c_68, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.55  tff(c_76, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_18, c_68])).
% 3.44/1.55  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.44/1.55  tff(c_36, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.44/1.55  tff(c_40, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.44/1.55  tff(c_752, plain, (![A_98, B_99]: (k6_domain_1(A_98, B_99)=k1_tarski(B_99) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.55  tff(c_761, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_752])).
% 3.44/1.55  tff(c_766, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_761])).
% 3.44/1.55  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.44/1.55  tff(c_767, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_766, c_38])).
% 3.44/1.55  tff(c_782, plain, (![A_106, B_107]: (m1_subset_1(k6_domain_1(A_106, B_107), k1_zfmisc_1(A_106)) | ~m1_subset_1(B_107, A_106) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.55  tff(c_796, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_766, c_782])).
% 3.44/1.55  tff(c_802, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_796])).
% 3.44/1.55  tff(c_803, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_802])).
% 3.44/1.55  tff(c_1566, plain, (![B_159, A_160]: (~v1_subset_1(B_159, A_160) | v1_xboole_0(B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_160)) | ~v1_zfmisc_1(A_160) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.44/1.55  tff(c_1575, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_803, c_1566])).
% 3.44/1.55  tff(c_1593, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_767, c_1575])).
% 3.44/1.55  tff(c_1594, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_1593])).
% 3.44/1.55  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.55  tff(c_1602, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1594, c_2])).
% 3.44/1.55  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.55  tff(c_55, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.55  tff(c_59, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_55])).
% 3.44/1.55  tff(c_1625, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1602, c_59])).
% 3.44/1.55  tff(c_1638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1625])).
% 3.44/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  Inference rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Ref     : 0
% 3.44/1.55  #Sup     : 344
% 3.44/1.55  #Fact    : 0
% 3.44/1.55  #Define  : 0
% 3.44/1.55  #Split   : 3
% 3.44/1.55  #Chain   : 0
% 3.44/1.55  #Close   : 0
% 3.44/1.55  
% 3.44/1.55  Ordering : KBO
% 3.44/1.55  
% 3.44/1.55  Simplification rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Subsume      : 37
% 3.44/1.55  #Demod        : 189
% 3.44/1.55  #Tautology    : 160
% 3.44/1.55  #SimpNegUnit  : 23
% 3.44/1.55  #BackRed      : 21
% 3.44/1.55  
% 3.44/1.55  #Partial instantiations: 0
% 3.44/1.55  #Strategies tried      : 1
% 3.44/1.55  
% 3.44/1.55  Timing (in seconds)
% 3.44/1.55  ----------------------
% 3.44/1.56  Preprocessing        : 0.28
% 3.44/1.56  Parsing              : 0.14
% 3.44/1.56  CNF conversion       : 0.02
% 3.44/1.56  Main loop            : 0.45
% 3.44/1.56  Inferencing          : 0.17
% 3.44/1.56  Reduction            : 0.14
% 3.44/1.56  Demodulation         : 0.09
% 3.44/1.56  BG Simplification    : 0.03
% 3.44/1.56  Subsumption          : 0.08
% 3.44/1.56  Abstraction          : 0.03
% 3.44/1.56  MUC search           : 0.00
% 3.44/1.56  Cooper               : 0.00
% 3.44/1.56  Total                : 0.76
% 3.44/1.56  Index Insertion      : 0.00
% 3.44/1.56  Index Deletion       : 0.00
% 3.44/1.56  Index Matching       : 0.00
% 3.44/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
