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
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 197 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 ( 481 expanded)
%              Number of equality atoms :   20 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40,C_41),C_41)
      | r2_hidden('#skF_2'(A_39,B_40,C_41),C_41)
      | k3_xboole_0(A_39,B_40) = C_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_168,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_171,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43,B_43),B_43)
      | k3_xboole_0(A_42,B_43) = B_43 ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(A_29,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_59,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30)
      | v1_xboole_0(k3_xboole_0(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_28,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_28])).

tff(c_65,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_62])).

tff(c_66,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_4')
      | ~ r2_hidden(D_6,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_184,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(A_42,'#skF_3','#skF_3'),'#skF_4')
      | k3_xboole_0(A_42,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_171,c_77])).

tff(c_243,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_1'(A_54,B_55,C_56),B_55)
      | ~ r2_hidden('#skF_2'(A_54,B_55,C_56),B_55)
      | ~ r2_hidden('#skF_2'(A_54,B_55,C_56),A_54)
      | k3_xboole_0(A_54,B_55) = C_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_268,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_243])).

tff(c_300,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_307,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_168,c_300])).

tff(c_323,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_20])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_323])).

tff(c_331,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_335,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_331,c_77])).

tff(c_330,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = '#skF_3'
    | r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_429,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_431,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_429,c_8])).

tff(c_440,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_331,c_431])).

tff(c_459,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_20])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_459])).

tff(c_466,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_521,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_20])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  
% 2.31/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.31/1.34  
% 2.31/1.34  %Foreground sorts:
% 2.31/1.34  
% 2.31/1.34  
% 2.31/1.34  %Background operators:
% 2.31/1.34  
% 2.31/1.34  
% 2.31/1.34  %Foreground operators:
% 2.31/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.31/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.34  
% 2.61/1.35  tff(f_63, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.61/1.35  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.61/1.35  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.61/1.35  tff(f_51, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.61/1.35  tff(c_26, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.35  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.35  tff(c_155, plain, (![A_39, B_40, C_41]: (~r2_hidden('#skF_1'(A_39, B_40, C_41), C_41) | r2_hidden('#skF_2'(A_39, B_40, C_41), C_41) | k3_xboole_0(A_39, B_40)=C_41)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.35  tff(c_168, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_155])).
% 2.61/1.35  tff(c_171, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43, B_43), B_43) | k3_xboole_0(A_42, B_43)=B_43)), inference(resolution, [status(thm)], [c_16, c_155])).
% 2.61/1.35  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.35  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.35  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.35  tff(c_54, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(A_29, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.35  tff(c_59, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30) | v1_xboole_0(k3_xboole_0(A_30, B_31)))), inference(resolution, [status(thm)], [c_20, c_54])).
% 2.61/1.35  tff(c_28, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.35  tff(c_62, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_59, c_28])).
% 2.61/1.35  tff(c_65, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_62])).
% 2.61/1.35  tff(c_66, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32, c_65])).
% 2.61/1.35  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.35  tff(c_77, plain, (![D_6]: (r2_hidden(D_6, '#skF_4') | ~r2_hidden(D_6, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 2.61/1.35  tff(c_184, plain, (![A_42]: (r2_hidden('#skF_2'(A_42, '#skF_3', '#skF_3'), '#skF_4') | k3_xboole_0(A_42, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_171, c_77])).
% 2.61/1.35  tff(c_243, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_1'(A_54, B_55, C_56), B_55) | ~r2_hidden('#skF_2'(A_54, B_55, C_56), B_55) | ~r2_hidden('#skF_2'(A_54, B_55, C_56), A_54) | k3_xboole_0(A_54, B_55)=C_56)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.35  tff(c_268, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_184, c_243])).
% 2.61/1.35  tff(c_300, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_268])).
% 2.61/1.35  tff(c_307, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_168, c_300])).
% 2.61/1.35  tff(c_323, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_307, c_20])).
% 2.61/1.35  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_323])).
% 2.61/1.35  tff(c_331, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_268])).
% 2.61/1.35  tff(c_335, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_331, c_77])).
% 2.61/1.35  tff(c_330, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3' | r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_268])).
% 2.61/1.35  tff(c_429, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_330])).
% 2.61/1.35  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.35  tff(c_431, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_429, c_8])).
% 2.61/1.35  tff(c_440, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_331, c_431])).
% 2.61/1.35  tff(c_459, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_440, c_20])).
% 2.61/1.35  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_459])).
% 2.61/1.35  tff(c_466, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_330])).
% 2.61/1.35  tff(c_521, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_466, c_20])).
% 2.61/1.35  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_521])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 104
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 3
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 12
% 2.61/1.35  #Demod        : 20
% 2.61/1.35  #Tautology    : 32
% 2.61/1.35  #SimpNegUnit  : 9
% 2.61/1.35  #BackRed      : 1
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.27
% 2.61/1.35  Parsing              : 0.14
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.32
% 2.61/1.36  Inferencing          : 0.13
% 2.61/1.36  Reduction            : 0.07
% 2.61/1.36  Demodulation         : 0.05
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.08
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.62
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
