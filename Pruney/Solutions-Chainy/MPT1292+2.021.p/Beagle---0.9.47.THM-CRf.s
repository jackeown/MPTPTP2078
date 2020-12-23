%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:32 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 108 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_34,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_18])).

tff(c_99,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,k3_tarski(B_38))
      | ~ m1_setfam_1(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_99])).

tff(c_24,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | A_12 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_166,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54),B_55)
      | ~ r1_tarski(A_54,B_55)
      | A_54 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_43,c_166])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_12])).

tff(c_79,plain,(
    ! [A_30,B_31] : ~ r2_hidden(A_30,k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_197,plain,(
    ! [A_58] :
      ( ~ r1_tarski(A_58,'#skF_4')
      | A_58 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_173,c_85])).

tff(c_214,plain,(
    ! [A_59] :
      ( A_59 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_59) ) ),
    inference(resolution,[status(thm)],[c_105,c_197])).

tff(c_230,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_214])).

tff(c_30,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_237,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_30])).

tff(c_241,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48,c_237])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:47:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.92/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.92/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.92/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.20  
% 1.92/1.21  tff(f_85, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.92/1.21  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.21  tff(f_43, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.92/1.21  tff(f_47, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.92/1.21  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 1.92/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.21  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.21  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.21  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.92/1.21  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.92/1.21  tff(c_38, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.92/1.21  tff(c_32, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.92/1.21  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.21  tff(c_48, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 1.92/1.21  tff(c_34, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.92/1.21  tff(c_18, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.21  tff(c_44, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_18])).
% 1.92/1.21  tff(c_99, plain, (![A_37, B_38]: (r1_tarski(A_37, k3_tarski(B_38)) | ~m1_setfam_1(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.21  tff(c_105, plain, (![A_37]: (r1_tarski(A_37, '#skF_4') | ~m1_setfam_1('#skF_4', A_37))), inference(superposition, [status(thm), theory('equality')], [c_44, c_99])).
% 1.92/1.21  tff(c_24, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.21  tff(c_43, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | A_12='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 1.92/1.21  tff(c_166, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.21  tff(c_173, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54), B_55) | ~r1_tarski(A_54, B_55) | A_54='#skF_4')), inference(resolution, [status(thm)], [c_43, c_166])).
% 1.92/1.21  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.21  tff(c_46, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_12])).
% 1.92/1.21  tff(c_79, plain, (![A_30, B_31]: (~r2_hidden(A_30, k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.21  tff(c_85, plain, (![A_6]: (~r2_hidden(A_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_79])).
% 1.92/1.21  tff(c_197, plain, (![A_58]: (~r1_tarski(A_58, '#skF_4') | A_58='#skF_4')), inference(resolution, [status(thm)], [c_173, c_85])).
% 1.92/1.21  tff(c_214, plain, (![A_59]: (A_59='#skF_4' | ~m1_setfam_1('#skF_4', A_59))), inference(resolution, [status(thm)], [c_105, c_197])).
% 1.92/1.21  tff(c_230, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_214])).
% 1.92/1.21  tff(c_30, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.92/1.21  tff(c_237, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_230, c_30])).
% 1.92/1.21  tff(c_241, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48, c_237])).
% 1.92/1.21  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_241])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 42
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 0
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 2
% 1.92/1.21  #Demod        : 22
% 1.92/1.21  #Tautology    : 25
% 1.92/1.21  #SimpNegUnit  : 1
% 1.92/1.21  #BackRed      : 2
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.28
% 1.92/1.21  Parsing              : 0.15
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.15
% 1.92/1.21  Inferencing          : 0.06
% 1.92/1.21  Reduction            : 0.05
% 1.92/1.21  Demodulation         : 0.03
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.03
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.47
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
