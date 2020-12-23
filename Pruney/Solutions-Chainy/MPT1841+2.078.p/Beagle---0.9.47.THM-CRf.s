%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:38 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   59 (  83 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   81 ( 139 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    ! [A_12,A_52] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_52,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_118,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_124,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_130,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_124])).

tff(c_134,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_130])).

tff(c_44,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_135,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_44])).

tff(c_140,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_140])).

tff(c_159,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_153])).

tff(c_160,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_159])).

tff(c_348,plain,(
    ! [B_67,A_68] :
      ( ~ v1_subset_1(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_357,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_348])).

tff(c_372,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_135,c_357])).

tff(c_373,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_372])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(B_37)
      | B_37 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_382,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_373,c_72])).

tff(c_51,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_10])).

tff(c_401,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_57])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_401])).

tff(c_406,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.17/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.17/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.17/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.30  
% 2.47/1.32  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.47/1.32  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.47/1.32  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.47/1.32  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.47/1.32  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.47/1.32  tff(f_98, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.47/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.32  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.47/1.32  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.32  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.47/1.32  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.32  tff(c_114, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.47/1.32  tff(c_117, plain, (![A_12, A_52]: (~v1_xboole_0(A_12) | ~r2_hidden(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.47/1.32  tff(c_118, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_117])).
% 2.47/1.32  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.47/1.32  tff(c_42, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.47/1.32  tff(c_46, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.47/1.32  tff(c_124, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.47/1.32  tff(c_130, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_124])).
% 2.47/1.32  tff(c_134, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_130])).
% 2.47/1.32  tff(c_44, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.47/1.32  tff(c_135, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_44])).
% 2.47/1.32  tff(c_140, plain, (![A_59, B_60]: (m1_subset_1(k6_domain_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.47/1.32  tff(c_153, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_140])).
% 2.47/1.32  tff(c_159, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_153])).
% 2.47/1.32  tff(c_160, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_159])).
% 2.47/1.32  tff(c_348, plain, (![B_67, A_68]: (~v1_subset_1(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.32  tff(c_357, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_160, c_348])).
% 2.47/1.32  tff(c_372, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_135, c_357])).
% 2.47/1.32  tff(c_373, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_372])).
% 2.47/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.32  tff(c_69, plain, (![B_37, A_38]: (~v1_xboole_0(B_37) | B_37=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.32  tff(c_72, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.47/1.32  tff(c_382, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_373, c_72])).
% 2.47/1.32  tff(c_51, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.32  tff(c_10, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.32  tff(c_57, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_10])).
% 2.47/1.32  tff(c_401, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_57])).
% 2.47/1.32  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_401])).
% 2.47/1.32  tff(c_406, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_117])).
% 2.47/1.32  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_2])).
% 2.47/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  Inference rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Ref     : 0
% 2.47/1.32  #Sup     : 81
% 2.47/1.32  #Fact    : 0
% 2.47/1.32  #Define  : 0
% 2.47/1.32  #Split   : 2
% 2.47/1.32  #Chain   : 0
% 2.47/1.32  #Close   : 0
% 2.47/1.32  
% 2.47/1.32  Ordering : KBO
% 2.47/1.32  
% 2.47/1.32  Simplification rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Subsume      : 20
% 2.47/1.32  #Demod        : 43
% 2.47/1.32  #Tautology    : 36
% 2.47/1.32  #SimpNegUnit  : 12
% 2.47/1.32  #BackRed      : 16
% 2.47/1.32  
% 2.47/1.32  #Partial instantiations: 0
% 2.47/1.32  #Strategies tried      : 1
% 2.47/1.32  
% 2.47/1.32  Timing (in seconds)
% 2.47/1.32  ----------------------
% 2.47/1.32  Preprocessing        : 0.32
% 2.47/1.32  Parsing              : 0.17
% 2.47/1.32  CNF conversion       : 0.02
% 2.47/1.32  Main loop            : 0.24
% 2.47/1.32  Inferencing          : 0.08
% 2.47/1.32  Reduction            : 0.08
% 2.47/1.32  Demodulation         : 0.06
% 2.47/1.32  BG Simplification    : 0.02
% 2.47/1.32  Subsumption          : 0.04
% 2.47/1.32  Abstraction          : 0.01
% 2.47/1.32  MUC search           : 0.00
% 2.47/1.32  Cooper               : 0.00
% 2.47/1.32  Total                : 0.58
% 2.47/1.32  Index Insertion      : 0.00
% 2.47/1.32  Index Deletion       : 0.00
% 2.47/1.32  Index Matching       : 0.00
% 2.47/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
